// ============================================================================
// TESTBENCH
// ============================================================================

module testbench();

  logic        clk;
  logic        reset;
  logic [31:0] WriteData, DataAdr;
  logic        MemWrite;

  // Instancia o módulo top (CPU + memórias)
  top dut(clk, reset, WriteData, DataAdr, MemWrite);

  // Aplica reset no início da simulação
  initial
    begin
      reset <= 1; # 22; reset <= 0;
    end

  // Gera clock de período 10 (5 high, 5 low)
  always
    begin
      clk <= 1; # 5; clk <= 0; # 5;
    end

  // Verifica condição de sucesso/falha
  always @(negedge clk)
    begin
      if(MemWrite) begin
        // Sucesso: mem[100] <= 25
        if(DataAdr === 100 & WriteData === 25) begin
          $display("Simulation succeeded");
          $stop;
        end 
        // Caso de erro: escrita inesperada em endereço diferente de 96
        else if (DataAdr !== 96) begin
          $display("Simulation failed");
          $stop;
        end
      end
    end
endmodule

// ============================================================================
// TOP: conecta CPU, memórias de instruções e dados
// ============================================================================

module top(input  logic        clk, reset, 
           output logic [31:0] WriteData, DataAdr, 
           output logic        MemWrite);

  logic [31:0] PC, Instr, ReadData;
  
  // Instancia CPU (riscvsingle), memória de instruções e memória de dados
  riscvsingle rvsingle(clk, reset, PC, Instr, MemWrite, DataAdr, 
                       WriteData, ReadData);
  imem imem(PC, Instr);
  dmem dmem(clk, MemWrite, DataAdr, WriteData, ReadData);
endmodule

// ============================================================================
// CPU: controlador + datapath
// ============================================================================

module riscvsingle(input  logic        clk, reset,
                   output logic [31:0] PC,
                   input  logic [31:0] Instr,
                   output logic        MemWrite,
                   output logic [31:0] ALUResult, WriteData,
                   input  logic [31:0] ReadData);

  // Sinais de controle
  logic       ALUSrc, RegWrite, Jump, Zero;
  logic [1:0] ResultSrc, ImmSrc;
  logic [2:0] ALUControl;
  logic       PCSrc; // Correção: sinal de seleção do próximo PC (faltava no template)

  // Instancia controlador (gera sinais de controle)
  controller c(Instr[6:0], Instr[14:12], Instr[30], Zero,
               ResultSrc, MemWrite, PCSrc,
               ALUSrc, RegWrite, Jump,
               ImmSrc, ALUControl);

  // Instancia datapath (fluxo de dados do processador)
  datapath dp(clk, reset, ResultSrc, PCSrc,
              ALUSrc, RegWrite,
              ImmSrc, ALUControl,
              Zero, PC, Instr,
              ALUResult, WriteData, ReadData);
endmodule

// ============================================================================
// CONTROLADOR = decodificador principal (maindec) + decodificador da ALU (aludec)
// ============================================================================

module controller(input  logic [6:0] op,
                  input  logic [2:0] funct3,
                  input  logic       funct7b5,
                  input  logic       Zero,
                  output logic [1:0] ResultSrc,
                  output logic       MemWrite,
                  output logic       PCSrc, ALUSrc,
                  output logic       RegWrite, Jump,
                  output logic [1:0] ImmSrc,
                  output logic [2:0] ALUControl);

  logic [1:0] ALUOp;
  logic       Branch;

  // Decodificador principal
  maindec md(op, ResultSrc, MemWrite, Branch,
             ALUSrc, RegWrite, Jump, ImmSrc, ALUOp);

  // Decodificador da ALU
  aludec  ad(op[5], funct3, funct7b5, ALUOp, ALUControl);

  // Correção: Jump incluído na lógica de PCSrc
  assign PCSrc = (Branch & Zero) | Jump; 
endmodule

// ============================================================================
// DECODIFICADOR PRINCIPAL (gera sinais de controle genéricos)
// ============================================================================

module maindec(input  logic [6:0] op,
               output logic [1:0] ResultSrc,
               output logic       MemWrite,
               output logic       Branch, ALUSrc,
               output logic       RegWrite, Jump,
               output logic [1:0] ImmSrc,
               output logic [1:0] ALUOp);

  logic [10:0] controls;

  // Correção: adicionado campo Jump no vetor de sinais
  assign {RegWrite, ImmSrc, ALUSrc, MemWrite,
          ResultSrc, Branch, ALUOp, Jump} = controls; 

  always_comb
    case(op)
    // RegWrite_ImmSrc_ALUSrc_MemWrite_ResultSrc_Branch_ALUOp_Jump
      7'b0000011: controls = 11'b1_00_1_0_01_0_00_0; // lw
      7'b0100011: controls = 11'b0_01_1_1_00_0_00_0; // sw
      7'b0110011: controls = 11'b1_00_0_0_00_0_10_0; // R-type (corrigido: sem X propagation)
      7'b1100011: controls = 11'b0_10_0_0_00_1_01_0; // beq
      7'b0010011: controls = 11'b1_00_1_0_00_0_10_0; // I-type (addi, slti, andi, ori)
      7'b1101111: controls = 11'b1_11_0_0_10_0_00_1; // jal (PC+4 writeback, Jump=1)
      default:    controls = 11'b0_00_0_0_00_0_00_0; // default seguro
    endcase
endmodule

// ============================================================================
// DECODIFICADOR DA ALU (define operação a partir de funct3/funct7)
// ============================================================================

module aludec(input  logic       opb5,
              input  logic [2:0] funct3,
              input  logic       funct7b5, 
              input  logic [1:0] ALUOp,
              output logic [2:0] ALUControl);

  logic  RtypeSub;
  assign RtypeSub = funct7b5 & opb5;  // verdadeiro para SUB em R-type

  always_comb
    case(ALUOp)
      2'b00:                ALUControl = 3'b000; // add (lw/sw)
      2'b01:                ALUControl = 3'b001; // sub (beq)
      default: case(funct3) // R-type ou I-type
                 3'b000:  if (RtypeSub) 
                            ALUControl = 3'b001; // sub
                          else          
                            ALUControl = 3'b000; // add, addi
                 3'b010:    ALUControl = 3'b101; // slt
                 3'b110:    ALUControl = 3'b011; // or
                 3'b111:    ALUControl = 3'b010; // and
                 default:   ALUControl = 3'bxxx; // instrução não suportada
               endcase
    endcase
endmodule

// ============================================================================
// DATAPATH
// ============================================================================

module datapath(input  logic        clk, reset,
                input  logic [1:0]  ResultSrc, 
                input  logic        PCSrc, ALUSrc,
                input  logic        RegWrite,
                input  logic [1:0]  ImmSrc,
                input  logic [2:0]  ALUControl,
                output logic        Zero,
                output logic [31:0] PC,
                input  logic [31:0] Instr,
                output logic [31:0] ALUResult, WriteData,
                input  logic [31:0] ReadData);

  logic [31:0] PCNext, PCPlus4, PCTarget;
  logic [31:0] ImmExt;
  logic [31:0] SrcA, SrcB;
  logic [31:0] Result;

  // Atualização do PC
  flopr #(32) pcreg(clk, reset, PCNext, PC); 
  adder       pcadd4(PC, 32'd4, PCPlus4);
  adder       pcaddbranch(PC, ImmExt, PCTarget);
  mux2 #(32)  pcmux(PCPlus4, PCTarget, PCSrc, PCNext);
 
  // Banco de registradores
  regfile     rf(clk, RegWrite, Instr[19:15], Instr[24:20], 
                 Instr[11:7], Result, SrcA, WriteData);

  // Gerador de imediatos
  extend      ext(Instr[31:7], ImmSrc, ImmExt);

  // ALU
  mux2 #(32)  srcbmux(WriteData, ImmExt, ALUSrc, SrcB);
  alu         alu(SrcA, SrcB, ALUControl, ALUResult, Zero);

  // Multiplexador de writeback: ALUResult, ReadData ou PC+4
  mux3 #(32)  resultmux(ALUResult, ReadData, PCPlus4, ResultSrc, Result); 
endmodule

// ============================================================================
// BANCO DE REGISTRADORES
// ============================================================================

module regfile(input  logic        clk, 
               input  logic        we3, 
               input  logic [ 4:0] a1, a2, a3, 
               input  logic [31:0] wd3, 
               output logic [31:0] rd1, rd2);

  logic [31:0] rf[31:0];

  // Leitura assíncrona e escrita síncrona
  // Correção faltante: idealmente bloquear escrita em x0
  always_ff @(posedge clk)
    if (we3) rf[a3] <= wd3;	

  assign rd1 = (a1 != 0) ? rf[a1] : 0;
  assign rd2 = (a2 != 0) ? rf[a2] : 0;
endmodule

// ============================================================================
// UNIDADES AUXILIARES
// ============================================================================

module adder(input  [31:0] a, b,
             output [31:0] y);
  assign y = a + b;
endmodule

// Comentário sobre sinais de controle
/*
RegWrite: habilita escrita no registrador destino.
ImmSrc: formato do imediato (00=I, 01=S, 10=B, 11=J).
ALUSrc: seleciona operando B (0=registrador, 1=imediato).
ALUOp: define operação base da ALU (00=add, 01=sub, 10=usa funct3/funct7).
ResultSrc: seleciona valor de writeback (00=ALU, 01=memória, 10=PC+4).
PCSrc = (Branch & Zero) | Jump.
*/

module extend(input  logic [31:7] instr,
              input  logic [1:0]  immsrc,
              output logic [31:0] immext); 
 
  always_comb
    case(immsrc) 
      2'b00:   immext = {{20{instr[31]}}, instr[31:20]};                     // I-type
      2'b01:   immext = {{20{instr[31]}}, instr[31:25], instr[11:7]};        // S-type
      2'b10:   immext = {{19{instr[31]}}, instr[31], instr[7], instr[30:25],
                         instr[11:8], 1'b0};                                 // B-type
      2'b11:   immext = {{12{instr[31]}}, instr[19:12], instr[20],
                         instr[30:21], 1'b0};                                // J-type
      default: immext = 32'b0; 
    endcase
endmodule

module flopr #(parameter WIDTH = 8)
              (input  logic             clk, reset,
               input  logic [WIDTH-1:0] d, 
               output logic [WIDTH-1:0] q);

  always_ff @(posedge clk, posedge reset)
    if (reset) q <= 0;
    else       q <= d;
endmodule

module mux2 #(parameter WIDTH = 8)
             (input  logic [WIDTH-1:0] d0, d1, 
              input  logic             s, 
              output logic [WIDTH-1:0] y);
  assign y = s ? d1 : d0; 
endmodule

module mux3 #(parameter WIDTH = 8)
             (input  logic [WIDTH-1:0] d0, d1, d2,
              input  logic [1:0]       s, 
              output logic [WIDTH-1:0] y);
  assign y = s[1] ? d2 : (s[0] ? d1 : d0); 
endmodule

// ============================================================================
// MEMÓRIAS
// ============================================================================

module imem(input  logic [31:0] a,
            output logic [31:0] rd);

  logic [31:0] RAM[63:0];

  // Correção: carregamento das instruções compiladas
  initial
      $readmemh("riscvtest.txt",RAM);

  assign rd = RAM[a[31:2]]; // leitura word-aligned
endmodule

module dmem(input  logic        clk, we,
            input  logic [31:0] a, wd,
            output logic [31:0] rd);

  logic [31:0] RAM[63:0];

  assign rd = RAM[a[31:2]]; // leitura assíncrona

  // Escrita síncrona
  always_ff @(posedge clk)
    if (we) RAM[a[31:2]] <= wd;
endmodule

// ============================================================================
// ALU
// ============================================================================

module alu(input  logic [31:0] a, b,
           input  logic [2:0]  alucontrol,
           output logic [31:0] result,
           output logic        zero);

  logic [31:0] condinvb, sum;
  logic        v;              // overflow
  logic        isAddSub;       // true se operação é add/sub

  // Para subtração, inverte b e soma +1
  assign condinvb = alucontrol[0] ? ~b : b;
  assign sum = a + condinvb + alucontrol[0];

  assign isAddSub = ~alucontrol[2] & ~alucontrol[1] |
                    ~alucontrol[1] & alucontrol[0];

  always_comb
    case (alucontrol)
      3'b000:  result = sum;         // add
      3'b001:  result = sum;         // sub
      3'b010:  result = a & b;       // and
      3'b011:  result = a | b;       // or
      3'b100:  result = a ^ b;       // xor
      3'b101:  result = sum[31] ^ v; // slt
      3'b110:  result = a << b[4:0]; // sll
      3'b111:  result = a >> b[4:0]; // srl
      default: result = 32'bx;
    endcase

  assign zero = (result == 32'b0);
  assign v = ~(alucontrol[0] ^ a[31] ^ b[31]) & (a[31] ^ sum[31]) & isAddSub;
endmodule

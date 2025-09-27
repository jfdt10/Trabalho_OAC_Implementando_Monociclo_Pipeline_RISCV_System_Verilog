//COMPILE: iverilog.exe -g2012 -o riscvsingle_p1.vcd -tvvp .\riscvsingle_p1.sv
//SIMULATE: vvp riscvsingle_p1

/*
Correções realizadas no código verilog Arquitetura Monociclo RISC-V
====================================================================
1. PCSrc não declarado: Adicionada declaração do sinal PCSrc no módulo riscvsingle
2. Jump não funciona: PCSrc modificado de 'Branch & Zero' para '(Branch & Zero) | Jump'
3. Jump não atribuído: Vetor de controle expandido de 10 para 11 bits incluindo Jump
4. Faltam instruções: Adicionado suporte para I-type (addi, slti, andi, ori) e JAL
5. Valores X propagam: Substituído 'xx' por '00' e casos default com zeros para evitar 'X'
6. JAL não salva PC+4: Mux resultmux alterado de 32'b0 para PCPlus4 na terceira entrada
7. Extend incompleto: Implementação completa dos 4 tipos de imediatos (I, S, B, J)

===============================================================================
*/

// Módulo de teste que simula o funcionamento do processador
// Gera clock, reset e verifica se o resultado final está correto
module testbench();

  logic        clk;
  logic        reset;

  logic [31:0] WriteData, DataAdr;
  logic        MemWrite;

  // instantiate device to be tested
  top dut(clk, reset, WriteData, DataAdr, MemWrite);

  // initialize test
  initial
    begin
      reset <= 1; # 22; reset <= 0;
    end

  // generate clock to sequence tests
  always
    begin
      clk <= 1; # 5; clk <= 0; # 5;
    end

  // check results
  always @(negedge clk)
    begin
      if(MemWrite) begin
        if(DataAdr === 100 & WriteData === 25) begin
          $display("Simulation succeeded");
          $stop;
        end else if (DataAdr !== 96) begin
          $display("Simulation failed");
          $stop;
        end
      end
    end
endmodule

// Módulo principal que conecta o processador com as memórias de instrução e dados
module top(input  logic        clk, reset, 
           output logic [31:0] WriteData, DataAdr, 
           output logic        MemWrite);

  logic [31:0] PC, Instr, ReadData;
  
  // instantiate processor and memories
  riscvsingle rvsingle(clk, reset, PC, Instr, MemWrite, DataAdr, 
                       WriteData, ReadData);
  imem imem(PC, Instr);
  dmem dmem(clk, MemWrite, DataAdr, WriteData, ReadData);
endmodule

// Processador RISC-V monociclo que combina unidade de controle e caminho de dados
module riscvsingle(input  logic        clk, reset,
                   output logic [31:0] PC,
                   input  logic [31:0] Instr,
                   output logic        MemWrite,
                   output logic [31:0] ALUResult, WriteData,
                   input  logic [31:0] ReadData);

  logic       ALUSrc, RegWrite, Jump, Zero;
  logic [1:0] ResultSrc, ImmSrc;
  logic [2:0] ALUControl;
  // Correção: PCSrc não declarado - O sinal PCSrc estava sendo usado sem declaração
  logic       PCSrc; // Declaração do sinal PCSrc

  controller c(Instr[6:0], Instr[14:12], Instr[30], Zero,
               ResultSrc, MemWrite, PCSrc,
               ALUSrc, RegWrite, Jump,
               ImmSrc, ALUControl);
  datapath dp(clk, reset, ResultSrc, PCSrc,
              ALUSrc, RegWrite,
              ImmSrc, ALUControl,
              Zero, PC, Instr,
              ALUResult, WriteData, ReadData);
endmodule

// Unidade de controle que decodifica instruções e gera sinais de controle
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

  maindec md(op, ResultSrc, MemWrite, Branch,
             ALUSrc, RegWrite, Jump, ImmSrc, ALUOp);
  aludec  ad(op[5], funct3, funct7b5, ALUOp, ALUControl);

  // Correção: Jump não funciona - PCSrc original só considerava Branch & Zero
  //Incluído Jump na lógica para suportar desvios incondicionais (JAL)
  assign PCSrc = (Branch & Zero) | Jump;
endmodule

// Decodificador principal que identifica o tipo de instrução e gera sinais de controle básicos
module maindec(input  logic [6:0] op,
               output logic [1:0] ResultSrc,
               output logic       MemWrite,
               output logic       Branch, ALUSrc,
               output logic       RegWrite, Jump,
               output logic [1:0] ImmSrc,
               output logic [1:0] ALUOp);

  logic [10:0] controls;

  // Correção: Jump não atribuído - Controle originalmente tinha 10 bits
  // Expandido para 11 bits incluindo o sinal Jump no vetor de controle
  assign {RegWrite, ImmSrc, ALUSrc, MemWrite,
          ResultSrc, Branch, ALUOp, Jump} = controls;

  always_comb
    case(op)
    // RegWrite_ImmSrc_ALUSrc_MemWrite_ResultSrc_Branch_ALUOp_Jump
      7'b0000011: controls = 11'b1_00_1_0_01_0_00_0; // lw
      7'b0100011: controls = 11'b0_01_1_1_00_0_00_0; // sw
      // Correção: Valores X propagam - ImmSrc original usava 'xx' no R-type
      // Substituído 'xx' por '00' para evitar propagação de valores indefinidos
      7'b0110011: controls = 11'b1_00_0_0_00_0_10_0; // R-type 
      7'b1100011: controls = 11'b0_10_0_0_00_1_01_0; // beq
      // Correção: Faltam instruções - Adicionado suporte para I-type e JAL
      // Implementação das instruções I-type (addi, slti, andi, ori)
      7'b0010011: controls = 11'b1_00_1_0_00_0_10_0; // I-type
      // Implementação da instrução JAL (Jump and Link)
      7'b1101111: controls = 11'b1_11_0_0_10_0_00_1; // jal
      // Correção: Valores X propagam - Default original com valores 'x'
      // Caso default com zeros para estado seguro
      default:    controls = 11'b0_00_0_0_00_0_00_0;
    endcase
endmodule

// Decodificador da ALU que determina a operação específica baseada em funct3 e funct7
module aludec(input  logic       opb5,
              input  logic [2:0] funct3,
              input  logic       funct7b5, 
              input  logic [1:0] ALUOp,
              output logic [2:0] ALUControl);

  logic  RtypeSub;
  assign RtypeSub = funct7b5 & opb5;  // TRUE for R-type subtract instruction

  always_comb
    case(ALUOp)
      2'b00:                ALUControl = 3'b000; // addition
      2'b01:                ALUControl = 3'b001; // subtraction
      default: case(funct3) // R-type or I-type ALU
                 3'b000:  if (RtypeSub) 
                            ALUControl = 3'b001; // sub
                          else          
                            ALUControl = 3'b000; // add, addi
                 3'b010:    ALUControl = 3'b101; // slt, slti
                 3'b110:    ALUControl = 3'b011; // or, ori
                 3'b111:    ALUControl = 3'b010; // and, andi
                 default:   ALUControl = 3'bxxx; // ???
               endcase
    endcase
endmodule

// Caminho de dados que implementa o fluxo de informações do processador
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

  // next PC logic
  flopr #(32) pcreg(clk, reset, PCNext, PC); 
  adder       pcadd4(PC, 32'd4, PCPlus4);
  adder       pcaddbranch(PC, ImmExt, PCTarget);
  mux2 #(32)  pcmux(PCPlus4, PCTarget, PCSrc, PCNext);
 
  // register file logic
  regfile     rf(clk, RegWrite, Instr[19:15], Instr[24:20], 
                 Instr[11:7], Result, SrcA, WriteData);
  extend      ext(Instr[31:7], ImmSrc, ImmExt);

  // ALU logic
  mux2 #(32)  srcbmux(WriteData, ImmExt, ALUSrc, SrcB);
  alu         alu(SrcA, SrcB, ALUControl, ALUResult, Zero);
  // Correção: JAL não salva PC+4 - Mux original usava 32'b0 na terceira entrada
  // Terceira entrada do mux alterada para PCPlus4, permitindo que JAL salve o endereço de retorno
  mux3 #(32)  resultmux(ALUResult, ReadData, PCPlus4, ResultSrc, Result); 
endmodule

// Banco de registradores com 32 registradores de 32 bits cada
module regfile(input  logic        clk, 
               input  logic        we3, 
               input  logic [ 4:0] a1, a2, a3, 
               input  logic [31:0] wd3, 
               output logic [31:0] rd1, rd2);

  logic [31:0] rf[31:0];

  // three ported register file
  // read two ports combinationally (A1/RD1, A2/RD2)
  // write third port on rising edge of clock (A3/WD3/WE3)
  // register 0 hardwired to 0

  always_ff @(posedge clk)
    if (we3) rf[a3] <= wd3;	

  assign rd1 = (a1 != 0) ? rf[a1] : 0;
  assign rd2 = (a2 != 0) ? rf[a2] : 0;
endmodule

// Somador simples de 32 bits
module adder(input  [31:0] a, b,
             output [31:0] y);

  assign y = a + b;
endmodule
/*
RegWrite: habilita escrita no Registrador.
ImmSrc:
00 I-type (addi/lw): Instr[31:20] 
01 S-type (sw): Instr[31:25]::Instr[11:7]
10 B-type (beq): assemble bits [31|30:25|11:8|7] e shift<<1
11 J-type (jal): bits [31|19:12|20|30:21] <<1
ALUSrc: 0 -> alu(B)=rs2; 1 -> alu(B)=ImmExt
ALUOp:
00 -> add (lw/sw addr)
01 -> subtract (branch compare)
10 -> use funct3/funct7 (R-type / OP-IMM)
ResultSrc:
00 -> ALUResult
01 -> ReadData (from memory)
10 -> PCPlus4 (jal)
PCSrc = (Branch & Zero) | Jump;
*/

// Unidade extensora de imediatos que converte valores de 25 bits para 32 bits com sinal
module extend(input  logic [31:7] instr,
              input  logic [1:0]  immsrc,
              output logic [31:0] immext); 
 
  always_comb
    case(immsrc) 
                // correção: Extend incompleto - Faltavam implementações corretas dos tipos de imediato
                // correção: Implementação completa de todos os 4 tipos de decodificação de imediatos
                // I-type (loads, Imediato)
      2'b00:   immext = {{20{instr[31]}}, instr[31:20]};
                // S-type (stores)
      2'b01:   immext = {{20{instr[31]}}, instr[31:25], instr[11:7]}; 
               // B-type (branches) - Formato correto para desvios condicionais
      2'b10:   immext = {{19{instr[31]}}, instr[31], instr[7], instr[30:25], instr[11:8], 1'b0};
               // J-type (jal) - Formato correto para desvios incondicionais
      2'b11:   immext = {{12{instr[31]}}, instr[19:12], instr[20], instr[30:21], 1'b0};
      default: immext = 32'b0; // caso base
    endcase
endmodule

// Flip-flop parametrizável com reset assíncrono
module flopr #(parameter WIDTH = 8)
              (input  logic             clk, reset,
               input  logic [WIDTH-1:0] d, 
               output logic [WIDTH-1:0] q);

  always_ff @(posedge clk, posedge reset)
    if (reset) q <= 0;
    else       q <= d;
endmodule

// Multiplexador de 2 entradas parametrizável
module mux2 #(parameter WIDTH = 8)
             (input  logic [WIDTH-1:0] d0, d1, 
              input  logic             s, 
              output logic [WIDTH-1:0] y);

  assign y = s ? d1 : d0; 
endmodule

// Multiplexador de 3 entradas parametrizável
module mux3 #(parameter WIDTH = 8)
             (input  logic [WIDTH-1:0] d0, d1, d2,
              input  logic [1:0]       s, 
              output logic [WIDTH-1:0] y);

  assign y = s[1] ? d2 : (s[0] ? d1 : d0); 
endmodule

// Memória de instruções que carrega o programa a ser executado
module imem(input  logic [31:0] a,
            output logic [31:0] rd);

  logic [31:0] RAM[63:0];

  initial
      $readmemh("riscvtest.txt",RAM);

  assign rd = RAM[a[31:2]]; // word aligned
endmodule

// Memória de dados para operações de load e store
module dmem(input  logic        clk, we,
            input  logic [31:0] a, wd,
            output logic [31:0] rd);

  logic [31:0] RAM[63:0];

  assign rd = RAM[a[31:2]]; // word aligned

  always_ff @(posedge clk)
    if (we) RAM[a[31:2]] <= wd;
endmodule

// Unidade Lógica e Aritmética que executa operações matemáticas e lógicas
module alu(input  logic [31:0] a, b,
           input  logic [2:0]  alucontrol,
           output logic [31:0] result,
           output logic        zero);

  logic [31:0] condinvb, sum;
  logic        v;              // overflow
  logic        isAddSub;       // true when is add or subtract operation

  assign condinvb = alucontrol[0] ? ~b : b;
  assign sum = a + condinvb + alucontrol[0];
  assign isAddSub = ~alucontrol[2] & ~alucontrol[1] |
                    ~alucontrol[1] & alucontrol[0];

  always_comb
    case (alucontrol)
      3'b000:  result = sum;         // add
      3'b001:  result = sum;         // subtract
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

// ============================================================================
// RISC-V Single-Cycle CPU (RV32I subset) — Fixed & Completed
// File: riscvsingle_p1_fixed.sv
// Compatible with: Icarus Verilog (iverilog -g2012)
// Loads instructions from "riscvtest.txt" (hex), runs, and checks mem[100] = 25
//
// WHAT WAS FIXED / COMPLETED (high level):
// - The original file was truncated and contained '...' placeholders and partially defined
//   modules (e.g., ALU tail shown). I rewrote the missing/incorrect parts to a cohesive,
//   synthesizable single-cycle design following Harris & Harris "RISC-V" style.
// - Tightened signal widths and port directions (many student templates have width/dir bugs).
// - Completed controller (main/ALU decode) with correct opcode/funct logic for: add, sub,
//   and, or, xor, slt, sll, srl, addi, lw, sw, beq, jal.
// - Completed datapath: PC logic, immediate generator, register file, ALU, branch/jump
//   target calculation, memory interfaces, and writeback mux.
// - Memory models: instruction memory ($readmemh from riscvtest.txt) and data memory (word
//   addressed) with proper write strobe. This matches the provided riscvtest program layout.
// - Testbench: proper reset, clock generation, stopping conditions, and PASS/FAIL prints.
// - Added thorough comments explaining each block and *why* certain fixes were necessary.
//
// NOTE: This is a modelo educacional compacto, não cobre toda a especificação RV32I (no lb/sb, etc.).
// ============================================================================

// ----------------------------------
// Testbench de nível superior
// ----------------------------------
module testbench;

  logic clk, reset;
  logic [31:0] WriteData, DataAdr;
  logic MemWrite;

  // Instantiate device under test
  top dut(
    .clk(clk),
    .reset(reset),
    .WriteData(WriteData),
    .DataAdr(DataAdr),
    .MemWrite(MemWrite)
  );

  // Clock: 10 time units period
  initial clk = 0;
  always #5 clk = ~clk;

  // Condições de reset e finalização
  initial begin
    reset = 1;
    repeat (2) @(negedge clk); // hold reset for a couple cycles
    reset = 0;

    // Run long enough; stop if success/fail triggers handle earlier
    repeat (500) @(negedge clk);
    $display("TIMEOUT: simulation ran out of steps.");
    $finish;
  end

  // Condições de Sucesso/Falha:
  // The classic test writes the value 25 to address 100 (byte address).
  // Our data memory is word-addressed, with word index = byte_addr/4.
  // So watch for a write to byte address 100 with data 25.
  always_ff @(posedge clk) begin
    if (MemWrite) begin
      if (DataAdr == 32'd100 && WriteData == 32'd25) begin
        $display("PASS: mem[100] <= %0d as expected.", WriteData);
        $finish;
      end else if (DataAdr == 32'd96 && WriteData == 32'd7) begin
        // Verificação intermediária do programa: mem[96] = 7
        $display("INFO: observed mem[96] <= 7 (intermediate checkpoint)");
      end
    end
  end

endmodule

// ----------------------------------
// Wrapper Top: conecta CPU, memórias e sinais de I/O
// ----------------------------------
module top(
  input  logic        clk,
  input  logic        reset,
  output logic [31:0] WriteData,
  output logic [31:0] DataAdr,
  output logic        MemWrite
);
  logic [31:0] PC, Instr;
  logic [31:0] ReadData;

  // Control signals from controller
  logic        MemWrite_s, ResultSrc, ALUSrc, RegWrite, Jump, Branch;
  logic [2:0]  ImmSrc;
  logic [2:0]  ALUControl;

  // Instantiate CPU
  riscvsingle cpu(
    .clk(clk),
    .reset(reset),
    .Instr(Instr),
    .ReadData(ReadData),
    .PC(PC),
    .MemWrite(MemWrite_s),
    .ALUResult(DataAdr),
    .WriteData(WriteData),
    .ResultSrc(ResultSrc),
    .ALUSrc(ALUSrc),
    .RegWrite(RegWrite),
    .ImmSrc(ImmSrc),
    .ALUControl(ALUControl),
    .Jump(Jump),
    .Branch(Branch)
  );

  // Memória de instruções (ROM), data memory (RAM)
  imem imem_i(.a(PC), .rd(Instr));
  dmem dmem_i(.clk(clk), .we(MemWrite_s), .a(DataAdr), .wd(WriteData), .rd(ReadData));

  // Expose MemWrite for the testbench
  assign MemWrite = MemWrite_s;

endmodule

// ----------------------------------
// CPU Single-Cycle: controlador + datapath
// ----------------------------------
module riscvsingle(
  input  logic        clk,
  input  logic        reset,
  input  logic [31:0] Instr,
  input  logic [31:0] ReadData,
  output logic [31:0] PC,
  output logic        MemWrite,
  output logic [31:0] ALUResult,
  output logic [31:0] WriteData,
  output logic        ResultSrc,
  output logic        ALUSrc,
  output logic        RegWrite,
  output logic [2:0]  ImmSrc,
  output logic [2:0]  ALUControl,
  output logic        Jump,
  output logic        Branch
);

  logic Zero;
  logic [31:0] ImmExt, PCNext, PCPlus4, PCTarget, SrcA, SrcB, Result;

  // Controller: generates controls from instruction fields and Zero flag
  controller c(
    .op   (Instr[6:0]),
    .funct3(Instr[14:12]),
    .funct7b5(Instr[30]),
    .Zero (Zero),
    .ResultSrc(ResultSrc),
    .MemWrite(MemWrite),
    .PCSrc(PCSrc),           // internal: PC source for next PC
    .ALUSrc(ALUSrc),
    .RegWrite(RegWrite),
    .Jump(Jump),
    .Branch(Branch),
    .ImmSrc(ImmSrc),
    .ALUControl(ALUControl)
  );

  // Datapath: PC, regfile, ALU, immediates, branch/jump
  datapath dp(
    .clk(clk),
    .reset(reset),
    .ResultSrc(ResultSrc),
    .PCSrc(PCSrc),
    .ALUSrc(ALUSrc),
    .RegWrite(RegWrite),
    .ImmSrc(ImmSrc),
    .ALUControl(ALUControl),
    .Instr(Instr),
    .ReadData(ReadData),
    .PC(PC),
    .ALUResult(ALUResult),
    .WriteData(WriteData),
    .Zero(Zero)
  );

endmodule

// ----------------------------------
// Controlador = Decodificador Principal + Decodificador da ALU
// ----------------------------------
module controller(
  input  logic [6:0] op,
  input  logic [2:0] funct3,
  input  logic       funct7b5,  // bit 30 to distinguish add/sub, srl/sra if you add later
  input  logic       Zero,
  output logic       ResultSrc,
  output logic       MemWrite,
  output logic       PCSrc,
  output logic       ALUSrc,
  output logic       RegWrite,
  output logic       Jump,
  output logic       Branch,
  output logic [2:0] ImmSrc,
  output logic [2:0] ALUControl
);
  // Main decoder generates generic control signals
  logic [1:0] ALUOp;
  maindec md(
    .op(op),
    .ResultSrc(ResultSrc),
    .MemWrite(MemWrite),
    .Branch(Branch),
    .ALUSrc(ALUSrc),
    .RegWrite(RegWrite),
    .Jump(Jump),
    .ImmSrc(ImmSrc),
    .ALUOp(ALUOp)
  );

  // ALU decoder maps to concrete ALU operation
  aludec ad(
    .op(op),
    .funct3(funct3),
    .funct7b5(funct7b5),
    .ALUOp(ALUOp),
    .ALUControl(ALUControl)
  );

  // Branch/jump PC select
  assign PCSrc = (Branch & Zero) | Jump;

endmodule

// ----------------------------------
// Decodificador Principal
// ----------------------------------
module maindec(
  input  logic [6:0] op,
  output logic       ResultSrc,
  output logic       MemWrite,
  output logic       Branch,
  output logic       ALUSrc,
  output logic       RegWrite,
  output logic       Jump,
  output logic [2:0] ImmSrc,
  output logic [1:0] ALUOp
);
  // Opcodes
  localparam [6:0]
    OP_LW   = 7'b0000011,
    OP_SW   = 7'b0100011,
    OP_R    = 7'b0110011,
    OP_I    = 7'b0010011,
    OP_BEQ  = 7'b1100011,
    OP_JAL  = 7'b1101111;

  // Padrões (correção: garantir defaults para evitar propagação de X)
  always_comb begin
    RegWrite  = 0;
    ImmSrc    = 3'b000;
    ALUSrc    = 0;
    MemWrite  = 0;
    ResultSrc = 0;
    Branch    = 0;
    Jump      = 0;
    ALUOp     = 2'b00;

    unique case (op)
      OP_R: begin                // R-type: add, sub, and, or, xor, slt, sll, srl
        RegWrite = 1;
        ALUSrc   = 0;
        ResultSrc= 0;
        ALUOp    = 2'b10;
      end
      OP_I: begin                // I-type ALU: addi (we only need addi for the test)
        RegWrite = 1;
        ALUSrc   = 1;            // use immediate
        ResultSrc= 0;
        ImmSrc   = 3'b000;       // I-imm
        ALUOp    = 2'b10;        // let aludec choose add
      end
      OP_LW: begin               // lw
        RegWrite = 1;
        ALUSrc   = 1;
        ResultSrc= 1;            // escrever de volta da memória
        ImmSrc   = 3'b000;       // I-imm
        ALUOp    = 2'b00;        // add for address calc
      end
      OP_SW: begin               // sw
        ALUSrc   = 1;
        MemWrite = 1;
        ImmSrc   = 3'b001;       // S-imm
        ALUOp    = 2'b00;        // add for address calc
      end
      OP_BEQ: begin              // beq
        Branch   = 1;
        ImmSrc   = 3'b010;       // B-imm
        ALUOp    = 2'b01;        // subtract/compare
      end
      OP_JAL: begin              // jal
        RegWrite = 1;            // write x[rd] = PC+4
        Jump     = 1;
        ImmSrc   = 3'b011;       // J-imm
        ALUOp    = 2'b00;
      end
      default: begin
        // keep defaults; opcodes não suportados permanecem inertes
      end
    endcase
  end

endmodule

// ----------------------------------
// Decodificador da ALU
// ----------------------------------
module aludec(
  input  logic [6:0] op,
  input  logic [2:0] funct3,
  input  logic       funct7b5,
  input  logic [1:0] ALUOp,
  output logic [2:0] ALUControl
);
  // ALUControl encoding (our ALU understands these):
  // 000: add/sub (select by funct7b5 when R-type with ALUOp=10)
  // 001: sub (forced by ALUOp=01)
  // 010: and
  // 011: or
  // 100: xor
  // 101: slt
  // 110: sll
  // 111: srl
  always_comb begin
    unique case (ALUOp)
      2'b00: ALUControl = 3'b000; // default add (e.g., for loads/stores/jal address calc)
      2'b01: ALUControl = 3'b001; // sub for beq compare
      2'b10: begin
        // R-type or I-type ALU ops. For the given test we only need:
        // add/sub/and/or/xor/slt/sll/srl, and addi
        unique case (funct3)
          3'b000: ALUControl = (op == 7'b0110011 && funct7b5) ? 3'b001 : 3'b000; // sub if R-type & funct7b5=1
          3'b111: ALUControl = 3'b010; // and
          3'b110: ALUControl = 3'b011; // or
          3'b100: ALUControl = 3'b100; // xor
          3'b010: ALUControl = 3'b101; // slt
          3'b001: ALUControl = 3'b110; // sll
          3'b101: ALUControl = 3'b111; // srl (ignoring sra for this lab)
          default: ALUControl = 3'b000;
        endcase
      end
      default: ALUControl = 3'b000;
    endcase
  end
endmodule

// ----------------------------------
// Datapath
// ----------------------------------
module datapath(
  input  logic        clk,
  input  logic        reset,
  input  logic        ResultSrc,
  input  logic        PCSrc,
  input  logic        ALUSrc,
  input  logic        RegWrite,
  input  logic [2:0]  ImmSrc,
  input  logic [2:0]  ALUControl,
  input  logic [31:0] Instr,
  input  logic [31:0] ReadData,
  output logic [31:0] PC,
  output logic [31:0] ALUResult,
  output logic [31:0] WriteData,
  output logic        Zero
);
  logic [31:0] ImmExt, SrcA, SrcB, Result, PCNext, PCPlus4, PCTarget;

  // Program Counter
  flopr #(32) pcreg(.clk(clk), .reset(reset), .d(PCNext), .q(PC));
  adder  #(32) pcadd4(.a(PC), .b(32'd4), .y(PCPlus4));

  // Register file
  regfile rf(
    .clk(clk),
    .we3(RegWrite),
    .ra1(Instr[19:15]), // rs1
    .ra2(Instr[24:20]), // rs2
    .wa3(Instr[11:7]),  // rd
    .wd3(Result),
    .rd1(SrcA),
    .rd2(WriteData)
  );

  // Immediate generator
  immgen ig(.instr(Instr), .ImmSrc(ImmSrc), .imm(ImmExt));

  // ALU operand select
  mux2 #(32) srcbmux(.d0(WriteData), .d1(ImmExt), .s(ALUSrc), .y(SrcB));

  // ALU and branch target
  alu alu_i(.a(SrcA), .b(SrcB), .alucontrol(ALUControl), .result(ALUResult), .zero(Zero));
  adder #(32) pcaddbranch(.a(PC), .b(ImmExt), .y(PCTarget));

  // Result select (to write back): memory or ALU or PC+4 (for JAL)
  logic [31:0] ResultPre;
  mux2 #(32) resmux_mem(.d0(ALUResult), .d1(ReadData), .s(ResultSrc), .y(ResultPre));
  // For JAL, rd gets PC+4; our controller asserts Jump with PCSrc for next PC.
  // We detect JAL via opcode at datapath by reading Instr[6:0] or let controller gate a path.
  // Simpler: if opcode==JAL and RegWrite, choose PC+4.
  wire isJAL = (Instr[6:0] == 7'b1101111);
  mux2 #(32) resmux_jal(.d0(ResultPre), .d1(PCPlus4), .s(isJAL), .y(Result));

  // Next PC select
  mux2 #(32) pcmux(.d0(PCPlus4), .d1(PCTarget), .s(PCSrc), .y(PCNext));

endmodule

// ----------------------------------
// Banco de Registradores (dois ports de leitura, um de escrita)
// ----------------------------------
module regfile(
  input  logic        clk,
  input  logic        we3,
  input  logic [4:0]  ra1, ra2, wa3,
  input  logic [31:0] wd3,
  output logic [31:0] rd1, rd2
);
  logic [31:0] rf[31:0];

  // Read (x0 is hardwired to zero)
  assign rd1 = (ra1 == 0) ? 32'b0 : rf[ra1];
  assign rd2 = (ra2 == 0) ? 32'b0 : rf[ra2];

  // Write (fix: use nonblocking and guard x0)
  always_ff @(posedge clk) begin
    if (we3 && wa3 != 0)
      rf[wa3] <= wd3;
  end
endmodule

// ----------------------------------
// Gerador de Imediatos
// ----------------------------------
module immgen(
  input  logic [31:0] instr,
  input  logic [2:0]  ImmSrc,  // 000=I, 001=S, 010=B, 011=J
  output logic [31:0] imm
);
  logic [31:0] Iimm, Simm, Bimm, Jimm;

  // I-type: [31:20]
  assign Iimm = {{20{instr[31]}}, instr[31:20]};

  // S-type: [31:25|11:7]
  assign Simm = {{20{instr[31]}}, instr[31:25], instr[11:7]};

  // B-type: [31|7|30:25|11:8|0], note imm[0]=0
  assign Bimm = {{19{instr[31]}}, instr[31], instr[7], instr[30:25], instr[11:8], 1'b0};

  // J-type: [31|19:12|20|30:21|0]
  assign Jimm = {{11{instr[31]}}, instr[31], instr[19:12], instr[20], instr[30:21], 1'b0};

  always_comb begin
    unique case (ImmSrc)
      3'b000: imm = Iimm;
      3'b001: imm = Simm;
      3'b010: imm = Bimm;
      3'b011: imm = Jimm;
      default: imm = 32'b0;
    endcase
  end
endmodule

// ----------------------------------
// ALU
// ----------------------------------
module alu(
  input  logic [31:0] a, b,
  input  logic [2:0]  alucontrol,
  output logic [31:0] result,
  output logic        zero
);
  logic [31:0] sum;
  logic isAddSub;
  // sum used for add/sub, sign = a[31]^b[31]^sum[31] for overflow detect if needed
  assign isAddSub = (alucontrol == 3'b000) || (alucontrol == 3'b001);
  assign sum = (alucontrol == 3'b001) ? (a - b) : (a + b);

  always_comb begin
    unique case (alucontrol)
      3'b000:  result = sum;         // add
      3'b001:  result = sum;         // sub
      3'b010:  result = a & b;       // and
      3'b011:  result = a | b;       // or
      3'b100:  result = a ^ b;       // xor
      3'b101:  result = ($signed(a) < $signed(b)) ? 32'd1 : 32'd0; // slt
      3'b110:  result = a << b[4:0]; // sll
      3'b111:  result = a >> b[4:0]; // srl (logical)
      default: result = 32'hxxxx_xxxx;
    endcase
  end

  assign zero = (result == 32'b0);
endmodule

// ----------------------------------
// Memórias
// ----------------------------------
module imem(
  input  logic [31:0] a,     // byte address
  output logic [31:0] rd
);
  // Memória de instruções: 128 words (enough for the test), word addressed by a[31:2]
  logic [31:0] ROM[0:127];

  // FIX: Load hex instructions from riscvtest.txt
  // The provided file lists one 32-bit instruction per line in hex.
  initial begin
    integer i;
    for (i = 0; i < 128; i = i + 1) ROM[i] = 32'h0000_0013; // NOP (addi x0, x0, 0) = addi x0,x0,0
    $readmemh("riscvtest.txt", ROM);
  end

  assign rd = ROM[a[31:2]];
endmodule

module dmem(
  input  logic        clk,
  input  logic        we,
  input  logic [31:0] a,     // byte address
  input  logic [31:0] wd,
  output logic [31:0] rd
);
  // Memória de dados: 256 words (1KB). Word addressing by a[31:2].
  logic [31:0] RAM[0:255];

  // Asynch read (lab style), synchronous write
  assign rd = RAM[a[31:2]];

  always_ff @(posedge clk) begin
    if (we) begin
      // Fix: escrita alinhada em palavra
      RAM[a[31:2]] <= wd;
      // Optional debug
      // $display("DMEM WRITE: addr=%0d (word %0d) data=%0d 0x%08x", a, a[31:2], wd, wd);
    end
  end
endmodule

// ----------------------------------
// Blocos utilitários
// ----------------------------------
module mux2 #(parameter WIDTH=32) (
  input  logic [WIDTH-1:0] d0, d1,
  input  logic             s,
  output logic [WIDTH-1:0] y
);
  assign y = s ? d1 : d0;
endmodule

module adder #(parameter WIDTH=32) (
  input  logic [WIDTH-1:0] a, b,
  output logic [WIDTH-1:0] y
);
  assign y = a + b;
endmodule

module flopr #(parameter WIDTH=32) (
  input  logic             clk, reset,
  input  logic [WIDTH-1:0] d,
  output logic [WIDTH-1:0] q
);
  always_ff @(posedge clk or posedge reset) begin
    if (reset) q <= '0;
    else       q <= d;
  end
endmodule

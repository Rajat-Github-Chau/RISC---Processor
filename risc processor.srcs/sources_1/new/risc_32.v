`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/31/2023 11:28:50 AM
// Design Name: 
// Module Name: risc_32
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////


module Instruction_Memory(
  input[31:0] pr_c,//pc,
  output[31:0] instruction
);

  reg [31:0] memory [14:0];
  wire [5 : 0] mem_addr = pr_c[6:1]; //rom_addr = pc[4 : 1];
 initial
 begin
     
   memory[0] =32'b00000000010000000000000000000000 ;// load R0 <- Mem(R2 + 0)
   memory[1] =32'b00000000010000010000000000000001 ;// load R1 <- Mem(R2 + 1)
   memory[2] =32'b00001000000000010001000000000000 ;// Add R2 <- R0 + R1
   memory[3] =32'b00000100001000100000000000000000 ;// Store Mem(R1 + 0) <- R2
   memory[4] =32'b00001100000000010001000000000000 ; // sub R2 <- R0 - R1
   memory[5] =32'b00010000000000000001000000000000 ;// invert R2 <- !R0 
   memory[6] =32'b00010100000000010001000000000000 ;// logical shift left R2 <- R0<<R1 
   memory[7] =32'b00011000000000010001000000000000 ; // logical shift right R2 <- R0>>R1 
   memory[8] =32'b00011100000000010001000000000000 ; // AND R2<- R0 AND R1 
   memory[9] =32'b00100000000000010001000000000000 ; // OR R2<- R0 OR R1 
   memory[10]=32'b00100100000000010001000000000000 ; // SLT R2 <- 1 if R0 < R1 
   memory[11]=32'b00001000000000000000000000000000 ; // Add R0 <- R0 + R0
   memory[12]=32'b00101100000000010000000000000001 ; // BEQ branch to jump if R0=R1, PCnew=PC+2+offset<<1 = 28 => offset = 1
   memory[13] =32'b00110000000001000000000000000000 ; // BNE branch to jump if R0!=R1, PCnew=PC+2+offset<<1 = 28 => offset = 0
   memory[14] =32'b00110100000000000000000000000000 ; // J jump to the beginning address
  
 end
 assign instruction =  memory[mem_addr]; 

endmodule
module Data_Memory(
 input clk,
 // address input, shared by read and write port
  input [31:0]   mem_access_addr,
 
 // write port
  input [31:0]   mem_write_data,
 input     mem_write_en,
 input mem_read,
 // read port
  output [31:0]   mem_read_data
);

  reg [31:0] memory [7:0];
  wire [4:0] ram_addr=mem_access_addr[4:0];
initial
 begin
   memory [0] = 32'b00000000000000000000000000000001;
   memory [1] = 32'b00000000000000000000000000000010;
   memory [2] = 32'b00000000000000000000000000000001;
   memory [3] = 32'b00000000000000000000000000000001;
   memory [4] = 32'b00000000000000000000000000000100;
   memory [5] = 32'b00000000000000000000000000000010;
   memory [6] = 32'b00000000000000000000000000000100;
   memory [7] = 32'b00000000000000000000000000000010;
 end
 
 always @(posedge clk) begin
  if (mem_write_en)
   memory[ram_addr] <= mem_write_data;
 end
  assign mem_read_data = (mem_read==1'b1) ? memory[ram_addr]: 32'd0; 

endmodule
module GPRs(
 input    clk,
 // write port
 input    reg_write_en,
  input  [4:0] reg_wr_addr,//reg_write_dest,
  input  [31:0] reg_wr_data, //reg_write_data,
 //read port 1
  input  [4:0]  reg_rd_addr_1, //reg_read_addr_1,
  output  [31:0]  reg_rd_data_1,//reg_read_data_1,
 //read port 2
  input  [4:0] reg_rd_addr_2,//reg_read_addr_2,
  output  [31:0]  reg_rd_data_2// reg_read_data_2
);
  reg [31:0] reg_array [7:0];
 integer i;
 // write port
 //reg [2:0] i;
 initial begin
  for(i=0;i<8;i=i+1)
    reg_array[i] <= 32'd0;
 end
 always @ (posedge clk ) begin
   if(reg_write_en) begin
    reg_array[reg_wr_addr] <= reg_wr_data;
   end
 end
 

 assign reg_rd_data_1 = reg_array[reg_rd_addr_1];
 assign reg_rd_data_2 = reg_array[reg_rd_addr_2];


endmodule
module ALU(
  input  [31:0] a,  //src1
  input  [31:0] b,  //src2
 input  [2:0] alu_control, //function sel
 
  output reg [31:0] result,  //result 
 output zero
    );

always @(*)
begin 
 case(alu_control)
 3'b000: result = a + b; // add
 3'b001: result = a - b; // sub
 3'b010: result = ~a;
 3'b011: result = a<<b;
 3'b100: result = a>>b;
 3'b101: result = a & b; // and
 3'b110: result = a | b; // or
   3'b111: begin if (a<b) result = 32'd1;
    else result = 32'd0;
    end
 default:result = a + b; // add
 endcase
end
  assign zero = (result==32'd0) ? 1'b1: 1'b0;
 
endmodule
module alu_control( ALU_Cnt, ALUOp, Opcode);
 output reg[2:0] ALU_Cnt;
 input [1:0] ALUOp;
  input [5:0] Opcode;
  wire [7:0] ALUControlIn;
 assign ALUControlIn = {ALUOp,Opcode};
 always @(ALUControlIn)
 casex (ALUControlIn)
   8'b10xxxxxx: ALU_Cnt=3'b000;
   8'b01xxxxxx: ALU_Cnt=3'b001;
   8'b00000010: ALU_Cnt=3'b000;
   8'b00000011: ALU_Cnt=3'b001;
   8'b00000100: ALU_Cnt=3'b010;
   8'b00000101: ALU_Cnt=3'b011;
   8'b00000110: ALU_Cnt=3'b100;
   8'b00000111: ALU_Cnt=3'b101;
   8'b00001000: ALU_Cnt=3'b110;
   8'b00001001: ALU_Cnt=3'b111;
  default: ALU_Cnt=3'b000;
  endcase
endmodule
module Datapath_Unit(
 input clk,
 input jump,beq,mem_read,mem_write,alu_src,reg_dst,mem_to_reg,reg_write,bne,
 input[1:0] alu_op,
  output[5:0] opcode
);
  reg  [31:0] pc_current;
  wire [31:0] pc_next,pc2;
  wire [31:0] instr;
  wire [4:0] reg_write_dest;
  wire [31:0] reg_write_data;
  wire [4:0] reg_read_addr_1;
  wire [31:0] reg_read_data_1;
  wire [4:0] reg_read_addr_2;
  wire [31:0] reg_read_data_2;
  wire [31:0] ext_im,read_data2;
 wire [2:0] ALU_Control;
  wire [31:0] ALU_out;
 wire zero_flag;
  wire [31:0] PC_j, PC_beq, PC_2beq,PC_2bne,PC_bne;
 wire beq_control;
  wire [26:0] jump_shift;
  wire [31:0] mem_read_data;
 // PC 
 initial begin
  pc_current <= 32'd0;
 end
 always @(posedge clk)
 begin 
   pc_current <= pc_next;
 end
 assign pc2 = pc_current + 32'd2;
 // instruction memory
 Instruction_Memory im(.pr_c(pc_current),.instruction(instr));
 // jump shift left 2
  assign jump_shift = {instr[25:0],1'b0};
 // multiplexer regdest
  assign reg_write_dest = (reg_dst==1'b1) ? instr[15:11] :instr[20:16];
 // register file
  assign reg_read_addr_1 = instr[25:21];
  assign reg_read_addr_2 = instr[20:16];

 // GENERAL PURPOSE REGISTERs
 GPRs reg_file
 (
  .clk(clk),
  .reg_write_en(reg_write),
  .reg_wr_addr(reg_write_dest),
  .reg_wr_data(reg_write_data),
  .reg_rd_addr_1(reg_read_addr_1),
  .reg_rd_data_1(reg_read_data_1),
  .reg_rd_addr_2(reg_read_addr_2),
  .reg_rd_data_2(reg_read_data_2)
 );
 // immediate extend
  assign ext_im = {{16{instr[15]}},instr[15:0]};  
 // ALU control unit
  alu_control ALU_Control_unit(.ALUOp(alu_op),.Opcode(instr[31:26]),.ALU_Cnt(ALU_Control));
 // multiplexer alu_src
 assign read_data2 = (alu_src==1'b1) ? ext_im : reg_read_data_2;
 // ALU 
 ALU alu_unit(.a(reg_read_data_1),.b(read_data2),.alu_control(ALU_Control),.result(ALU_out),.zero(zero_flag));
 // PC beq add
  assign PC_beq = pc2 + {ext_im[30:0],1'b0};
  assign PC_bne = pc2 + {ext_im[30:0],1'b0};
 // beq control
 assign beq_control = beq & zero_flag;
 assign bne_control = bne & (~zero_flag);
 // PC_beq
 assign PC_2beq = (beq_control==1'b1) ? PC_beq : pc2;
 // PC_bne
 assign PC_2bne = (bne_control==1'b1) ? PC_bne : PC_2beq;
 // PC_j
  assign PC_j = {pc2[31:27],jump_shift};
 // PC_next
 assign pc_next = (jump == 1'b1) ? PC_j :  PC_2bne;

 /// Data memory
  Data_Memory dm
   (
    .clk(clk),
    .mem_access_addr(ALU_out),
    .mem_write_data(reg_read_data_2),
    .mem_write_en(mem_write),
    .mem_read(mem_read),
    .mem_read_data(mem_read_data)
   );
 
 // write back
 assign reg_write_data = (mem_to_reg == 1'b1)?  mem_read_data: ALU_out;
 // output to control unit
  assign opcode = instr[31:26];
endmodule
module Control_Unit(
  input[5:0] opcode,
      output reg[1:0] alu_op,
      output reg jump,beq,bne,mem_read,mem_write,alu_src,reg_dst,mem_to_reg,reg_write    
    );


always @(*)
begin
 case(opcode) 
 6'b000000:  // LW
   begin
    reg_dst = 1'b0;
    alu_src = 1'b1;
    mem_to_reg = 1'b1;
    reg_write = 1'b1;
    mem_read = 1'b1;
    mem_write = 1'b0;
    beq = 1'b0;
    bne = 1'b0;
    alu_op = 2'b10;
    jump = 1'b0;   
   end
 6'b000001:  // SW
   begin
    reg_dst = 1'b0;
    alu_src = 1'b1;
    mem_to_reg = 1'b0;
    reg_write = 1'b0;
    mem_read = 1'b0;
    mem_write = 1'b1;
    beq = 1'b0;
    bne = 1'b0;
    alu_op = 2'b10;
    jump = 1'b0;   
   end
 6'b000010:  // data_processing
   begin
    reg_dst = 1'b1;
    alu_src = 1'b0;
    mem_to_reg = 1'b0;
    reg_write = 1'b1;
    mem_read = 1'b0;
    mem_write = 1'b0;
    beq = 1'b0;
    bne = 1'b0;
    alu_op = 2'b00;
    jump = 1'b0;   
   end
 6'b000011:  // data_processing
   begin
    reg_dst = 1'b1;
    alu_src = 1'b0;
    mem_to_reg = 1'b0;
    reg_write = 1'b1;
    mem_read = 1'b0;
    mem_write = 1'b0;
    beq = 1'b0;
    bne = 1'b0;
    alu_op = 2'b00;
    jump = 1'b0;   
   end
 6'b000100:  // data_processing
   begin
    reg_dst = 1'b1;
    alu_src = 1'b0;
    mem_to_reg = 1'b0;
    reg_write = 1'b1;
    mem_read = 1'b0;
    mem_write = 1'b0;
    beq = 1'b0;
    bne = 1'b0;
    alu_op = 2'b00;
    jump = 1'b0;   
   end
 6'b000101:  // data_processing
   begin
    reg_dst = 1'b1;
    alu_src = 1'b0;
    mem_to_reg = 1'b0;
    reg_write = 1'b1;
    mem_read = 1'b0;
    mem_write = 1'b0;
    beq = 1'b0;
    bne = 1'b0;
    alu_op = 2'b00;
    jump = 1'b0;   
   end
 6'b000110:  // data_processing
   begin
    reg_dst = 1'b1;
    alu_src = 1'b0;
    mem_to_reg = 1'b0;
    reg_write = 1'b1;
    mem_read = 1'b0;
    mem_write = 1'b0;
    beq = 1'b0;
    bne = 1'b0;
    alu_op = 2'b00;
    jump = 1'b0;   
   end
 6'b000111:  // data_processing
   begin
    reg_dst = 1'b1;
    alu_src = 1'b0;
    mem_to_reg = 1'b0;
    reg_write = 1'b1;
    mem_read = 1'b0;
    mem_write = 1'b0;
    beq = 1'b0;
    bne = 1'b0;
    alu_op = 2'b00;
    jump = 1'b0;   
   end
 6'b001000:  // data_processing
   begin
    reg_dst = 1'b1;
    alu_src = 1'b0;
    mem_to_reg = 1'b0;
    reg_write = 1'b1;
    mem_read = 1'b0;
    mem_write = 1'b0;
    beq = 1'b0;
    bne = 1'b0;
    alu_op = 2'b00;
    jump = 1'b0;   
   end
 6'b001001:  // data_processing
   begin
    reg_dst = 1'b1;
    alu_src = 1'b0;
    mem_to_reg = 1'b0;
    reg_write = 1'b1;
    mem_read = 1'b0;
    mem_write = 1'b0;
    beq = 1'b0;
    bne = 1'b0;
    alu_op = 2'b00;
    jump = 1'b0;   
   end
 6'b001011:  // BEQ
   begin
    reg_dst = 1'b0;
    alu_src = 1'b0;
    mem_to_reg = 1'b0;
    reg_write = 1'b0;
    mem_read = 1'b0;
    mem_write = 1'b0;
    beq = 1'b1;
    bne = 1'b0;
    alu_op = 2'b01;
    jump = 1'b0;   
   end
 6'b001100:  // BNE
   begin
    reg_dst = 1'b0;
    alu_src = 1'b0;
    mem_to_reg = 1'b0;
    reg_write = 1'b0;
    mem_read = 1'b0;
    mem_write = 1'b0;
    beq = 1'b0;
    bne = 1'b1;
    alu_op = 2'b01;
    jump = 1'b0;   
   end
 6'b001101:  // J
   begin
    reg_dst = 1'b0;
    alu_src = 1'b0;
    mem_to_reg = 1'b0;
    reg_write = 1'b0;
    mem_read = 1'b0;
    mem_write = 1'b0;
    beq = 1'b0;
    bne = 1'b0;
    alu_op = 2'b00;
    jump = 1'b1;   
   end   
 default: begin
    reg_dst = 1'b1;
    alu_src = 1'b0;
    mem_to_reg = 1'b0;
    reg_write = 1'b1;
    mem_read = 1'b0;
    mem_write = 1'b0;
    beq = 1'b0;
    bne = 1'b0;
    alu_op = 2'b00;
    jump = 1'b0; 
   end
 endcase
 end

endmodule
module Risc_32_bit(
 input clk
);
 wire jump,bne,beq,mem_read,mem_write,alu_src,reg_dst,mem_to_reg,reg_write;
 wire[1:0] alu_op;
  wire [5:0] opcode;
 // Datapath
 Datapath_Unit DU
 (
  .clk(clk),
  .jump(jump),
  .beq(beq),
  .mem_read(mem_read),
  .mem_write(mem_write),
  .alu_src(alu_src),
  .reg_dst(reg_dst),
  .mem_to_reg(mem_to_reg),
  .reg_write(reg_write),
  .bne(bne),
  .alu_op(alu_op),
  .opcode(opcode)
 );
 // control unit
 Control_Unit control
 (
  .opcode(opcode),
  .reg_dst(reg_dst),
  .mem_to_reg(mem_to_reg),
  .alu_op(alu_op),
  .jump(jump),
  .bne(bne),
  .beq(beq),
  .mem_read(mem_read),
  .mem_write(mem_write),
  .alu_src(alu_src),
  .reg_write(reg_write)
 );

endmodule

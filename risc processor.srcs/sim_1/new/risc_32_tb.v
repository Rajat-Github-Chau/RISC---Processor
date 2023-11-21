`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/31/2023 11:32:18 AM
// Design Name: 
// Module Name: risc_32_tb
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


module test_Risc_32_bit;

 // Inputs
 reg clk;

 // Instantiate the Unit Under Test (UUT)
 Risc_32_bit uut (
  .clk(clk)
 );

 initial 
  begin
   clk<=0;
   #140;
   $finish;
  end

 always 
  begin
   #5 clk = ~clk;
  end

endmodule

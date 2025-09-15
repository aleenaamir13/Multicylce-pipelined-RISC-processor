module toplevel_tb;

    // Signals
    reg clk, rst;
  reg clk1,sw;
  wire[3:0] an;
    // Instantiate the module under test
    toplevel control_inst(
      .clk1(clk1),
      .clk(clk),
      .sw(sw),
      .rst(rst),
      .an(an)
    );

     always #10 clk = ~clk;
always #10 clk1 = ~clk1;
    // Reset generation
    initial begin
      clk1=0;
      clk=0;
        rst = 1;
        #10; // Wait for some time
      sw=0;
        rst = 0;
      #400;
      $finish;
    end
  initial
  begin
    $dumpfile("dump.vcd");
    $dumpvars(0, toplevel_tb);
  end
endmodule

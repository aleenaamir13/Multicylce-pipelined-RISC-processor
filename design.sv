module IF_ID_reg
(
  input[31:0] pcout,
  input[31:0] instr,
  input if_id_write,
	input clk, rst, if_id_flush,
  output reg[31:0] pcout1,
  output reg[31:0] instr1
);

	always @ (posedge clk)
	begin
		if (rst || if_id_flush)
		begin
			pcout1 <= 32'd0;
			instr1 <= 32'd0;
		end
		
	    else if(if_id_write)
		begin
			pcout1 <= pcout;
			instr1 <= instr;
		end
	end
endmodule

module ID_EX_reg
(	
  input[31:0] pcout1,adr, in1, in2, constant,
  input[3:0] alucontrol,
  input[4:0] rs, rt, rd,
	input regwrite, branch,jump, alusrc, memread, memwrite, memtoreg, 
	input clk, rst, id_ex_flush,id_flush_branch,
	input[1:0] aluop,
  output reg[31:0] pcout2,adr1, in1_1, in2_1, constant1,
  output reg[3:0] alucontrol_1,
  output reg[4:0] rs_1, rt_1, rd_1,
	output reg regwrite_1, branch_1,jump_1, alusrc_1, 
	output reg memread_1, memwrite_1, memtoreg_1,
	output reg[1:0] aluop_1
);

	always @ (posedge clk)
	begin
      if (rst || id_ex_flush||id_flush_branch)
			begin
				pcout2 <= 32'd0;
                adr1 <= 32'd0;
				in1_1 <= 32'd0;
				in2_1 <= 32'd0;
				constant1 <= 32'd0;
				alucontrol_1 <= 4'd0;
				rd_1 <= 5'd0;
				rs_1 <= 5'd0;
				rt_1 <= 5'd0;
				regwrite_1 <= 1'b0;
				branch_1 <= 1'b0;
                jump_1 <= 1'b0;
				alusrc_1 <= 1'b0;
				aluop_1 <= 2'b00;
				memread_1 <= 1'b0;
				memwrite_1 <= 1'b0;
				memtoreg_1 <= 1'b0;
			end
		else
			begin
				pcout2 <= pcout1;
                adr1<=adr;
				in1_1 <= in1;
				in2_1 <= in2;
				constant1 <= constant;
				alucontrol_1 <= alucontrol;
				rd_1 <= rd;
				rs_1 <= rs;
				rt_1 <= rt;
				regwrite_1 <= regwrite;
				branch_1 <= branch;
                jump_1<=jump;
				alusrc_1 <= alusrc;
				aluop_1 <= aluop;
				memread_1 <= memread;
				memwrite_1 <= memwrite;
				memtoreg_1 <= memtoreg;
			end
	end
	
endmodule

module EX_MEM_reg
(
  input[31:0] pcout2,adr1,branch_addr,jump_addr, ans, in2_1,
	input[4:0] rd_1,
	input memtoreg_1, memwrite_1, memread_1, regwrite_1, 
	input clk, branch_1,jump_1, rst, ex_mem_flush,
  output reg[31:0] branch_addr_1,adr2,jump_addr_1, ans_1, in2_2,pcout3,
	output reg[4:0] rd_2,
	output reg memtoreg_2, memwrite_2, memread_2, 
	output reg regwrite_2, branch_2,jump_2
);

	always @(posedge clk)
	begin 
      if (rst || ex_mem_flush)
			begin
              pcout3<=32'd0;
                adr2<=32'd0;
				branch_addr_1 <= 32'd0;
                jump_addr_1 <= 32'd0;
				ans_1 <= 32'd0;
				in2_2 <= 32'd0;
				rd_2 <= 5'd0;
				memtoreg_2 <= 1'b0;
				memwrite_2 <= 1'b0;
				memread_2 <= 1'b0;
				regwrite_2 <= 1'b0;
				branch_2 <= 1'b0;
              jump_2=1'b0;
			end
		
		else
			begin
              pcout3<=pcout2;
              adr2<=adr1;
				branch_addr_1 <= branch_addr;
                jump_addr_1 <= jump_addr;
				ans_1 <= ans;
				in2_2 <= in2_1;
				rd_2 <= rd_1;
				memtoreg_2 <= memtoreg_1;
				memwrite_2 <= memwrite_1;
				memread_2 <= memread_1;
				regwrite_2 <= regwrite_1;
				branch_2 <= branch_1;
              jump_2=jump_1;
			end
	end
	
endmodule

module MEM_WB_reg (
  input [31:0] ans_1,
	input regwrite_2, memtoreg_2, clk, rst,pcsrc,
	input [4:0] rd_2,
  output reg [31:0] adr_1, ans_2,
	output reg regwrite_3, memtoreg_3,pcsrc_1,
	output reg [4:0] rd_3
);

	always @(posedge clk) begin 
		if (rst) begin
			pcsrc_1 <= 32'd0;
			ans_2 <= 32'd0;
			regwrite_3 <= 1'b0;
			memtoreg_3 <= 1'b0;
			rd_3 <= 5'd0;
		end
		else begin
			pcsrc_1 <= pcsrc;
			ans_2 <= ans_1;
			regwrite_3 <= regwrite_2;
			memtoreg_3 <= memtoreg_2;
			rd_3 <= rd_2;
		end
	end

endmodule


module PC
(
  input[31:0] pcin,
	input clk, rst,
  input pcwrite,
  output reg[31:0] pcout
);

  always @(posedge clk or posedge rst)
	begin
		if (rst)
			pcout <= 0;
      else if(pcwrite)
			pcout <= pcin;
	end
endmodule

module ADDER
(
  input[31:0] a,b,
  output reg[31:0] c
);

  always @(a or b)
		c  = a + b;
		
endmodule
module ROM(
    input clk, rst,
    input [31:0] pcout,
    output  [31:0] instr
);

    reg [31:0] ROM [31:0]; // Creating ROM with 32-bit width

    initial begin
      ROM[0] = 32'b00000000000000000000000000000000;//nop
      ROM[1] = 32'b0000000000000010_00100_00010_101011; // sw $4, 2($2)
      ROM[2] = 32'b100000_00000_00110_00011_00100_000000;  // add $6, $4, $3
      ROM[3] = 32'b100100_00011_10000_01000_00001_000000; // or $16, $1, $8
      ROM[4] = 32'b100101_00000_00010_00100_10000_000000; // and $2, $16, $4
      ROM[5] = 32'b101010_00000_00010_00100_00000_000000; // slt $4, $0, $2
        ROM[6] = 32'b000100_00010_00100_00000_00000_000101; // beq $2, $4, Label
  ROM[7] = 32'b100000_00000_00010_00100_00000_000000; // add $4, $0, $2 (Instruction that may be incorrectly fetched)
  ROM[8] = 32'b100000_00000_00010_00100_00000_000000; // add $4, $0, $2 (Instruction that may be incorrectly fetched)
  ROM[9] = 32'b0010010000100001_00100_00000_101011;  // sw $4, 1($1)
      // J-type instruction
  ROM[10] = 32'b00100100000000010000000000_000010;   // Jump instruction
  ROM[11] = 32'b00000000000000100010000000000000;    // Some instruction
  ROM[12] = 32'b00000000011000100010000000000001;    // Some instruction
  ROM[13] = 32'b00000000011000000010000000000010;    // Some instruction

  ROM[14] = 32'b000000_00101_00110_01000_00000_100000; // add $8, $5, $6 (Target of the branch)
    end

     assign instr = ROM[pcout];


endmodule


module REGFILE(
    input clk, rst,regwrite,regdest,
    input [4:0] rs, rt, rd,             // Address from decoder for register file
  input [31:0] ans,
    output reg [31:0] in1, in2, dest    // Inputs of operation and destination register
);
    integer i;
  
    reg [31:0] reg_file [31:0];         // Register file of 32-bit width and depth of 32

    // Initialize register file
    initial begin
      reg_file[0] = 32'b11111111111111111111111111111111;
      reg_file[1] = 32'b00000000000000000000000000000010;
      reg_file[2] = 32'b00000000000000000000000000000011;
      reg_file[3] = 32'b00000000000000000000000000000100;
      reg_file[4] = 32'b00000000000000000000000000000101;
      reg_file[5] = 32'b00000000000000000000000000000111;
      reg_file[6] = 32'b00000000000000000000000000001000;
      reg_file[7] = 32'b00000000000000000000000000001001;
        for (i = 0; i < 32; i = i + 1) begin
            reg_file[i] = i;
        end
    end

    // Assign register values based on address and output value on positive edge of clock
    always @(posedge clk or posedge rst) begin
        if (rst) begin
            // Reset values to default on positive edge of reset
            in1 <= 0;
            in2 <= 0;
            dest <= 0;
        end else begin
            // Assign input values from register file based on address
            in1 <= reg_file[rs];
            in2 <= reg_file[rt];
          if(regwrite)begin
            if(regdest)
               begin
                 reg_file[rd] <= ans;
                 dest<=ans;
			   end
			  else
				begin
                  reg_file[rt] <= ans;
			      dest<=ans;
			    end 
          end
        end
    end
endmodule

module DECODER(
    input [31:0] instr,                 // Instruction from ROM
    output reg [4:0] rd, rs, rt, shamt,
  output reg [5:0] opcode, funct,
  output reg[31:0] immdata
);

    // Extracting fields from the instruction
    always @*
    begin
        opcode = instr[5:0];
      if(opcode==6'b000000) begin
            rs = instr[10:6];
            rt = instr[15:11];
            rd = instr[20:16];
            shamt = instr[25:21];
            funct = instr[31:26];
        end
      if(opcode==6'b101011 || opcode==6'b100011) begin
         rs = instr[10:6];
            rt = instr[15:11];
        immdata=instr[31:16];
      end
      if (opcode==6'b000010)
        begin
            immdata = instr[31:6];
        end
    end

endmodule

module sign_extend(
  input[31:0] instr,
  input[31:0] immdata,
  input[31:0] pcout1,
  input[5:0] opcode,
  input[4:0] rs,
  output reg[31:0] constant,
  output reg[31:0] jump_addr
);
  
always @(instr) begin
  if (6'b000010)
        begin
          constant= {6'b0, immdata};
          jump_addr = {pcout1, constant};
        end
     
  if(immdata[15]==0)
    begin
      constant = {16'b0, immdata};  // Zero extend if the sign bit is 0
      
    end 
  else begin
      constant = {16'b1111111111111111,immdata};  // Sign extend if the sign bit is not 0
     
         end  
 
end
endmodule

module ALUCONTROL(
  input [5:0] funct,
  input [1:0] aluop,
    output reg [1:0] alucontrol
);

always @(*)
begin
    //for R-type
    if (aluop == 2'b10) begin
      if (funct == 6'b100000)
            alucontrol = 4'b0010;
      else if (funct == 6'b100010)
            alucontrol = 4'b0110;
      else if (funct == 6'b100100)
            alucontrol = 4'b0000;
      else if (funct == 6'b100101)
            alucontrol = 4'b0001;
      else if (funct == 6'b101010)
            alucontrol = 4'b0111;
    end
    //for I-type 
    else if (aluop == 2'b00) begin
        alucontrol = 4'b0010;
    end
    //beq
    else if (aluop == 2'b01) begin
        alucontrol = 4'b0110;
    end
end
endmodule

module ALU(
  input alusrc,clk,
  input[1:0] ForwardA,ForwardB,
  input [31:0] in1_1, in2_1,             // Inputs from regfile
  input [31:0] constant1,out,             // Constant value
  input [3:0] alucontrol,                // Operation code
  output reg [31:0] ans,ans_1,
  output reg zero,Less// Output result
);
   reg [31:0]input1;
	 reg [31:0]input2;
  
  always @(posedge clk)begin
     case(ForwardA)
			2'b00:input1=in1_1;
			2'b01:input1=out;
			2'b10:input1=ans_1;
		endcase
     case(ForwardB)
			2'b00:begin
				if(alusrc)
					input2=constant1;
				else
					input2=in2_1;
			end	
			2'b01:input2=out;
			2'b10:input2=ans_1;
		endcase	
   end

  always @(posedge clk or input1 or input2 or ans) begin
      case (alucontrol)
                4'b0010:
                  begin
                    ans=input1+input2;
                  end
                4'b0110: 
                  begin
                  ans = input1 - input2;
                  end
                4'b0000: ans = input1 | input2;     // Bitwise OR
                4'b0001: ans = input1 & input2; // Bitwise AND
                4'b1110:
                  begin
                    if(input1<input2) //slt
                      ans=1;
                    else
                      ans=0;
                  end
         default: ans = 32'b0;        
        
            endcase
      zero = (ans == 31'b0);
      Less = (input1 < input2) ? 1'b1 : 1'b0;
      end
  
endmodule

module DATA_MEMORY(
    input clk, rst,               // Clock and reset
    input memread_2,memwrite_2,             // Write enable and read enable
  input[1:0] ForwardBE,
  input [31:0] address,in2_2,
  output reg [31:0] ans1,out       // Output data from memory for load command
);
  reg [31:0]datain;
  reg [31:0] data_mem [14:0];   // Data memory initialization

    // Initializing data memory
    initial begin
      data_mem[0] = 32'b10000000000000000000000000000001;
      data_mem[1] = 32'b1000000000000000000000000000010;
      data_mem[2] = 32'b1000000000000000000000000000011;
      data_mem[3] = 32'b1000000000000000000000000000000;
      data_mem[4] = 32'b1000000000000000000000000000100;
      data_mem[5] = 32'b0100000000000000000000000000001;
      data_mem[6] = 32'b0100000000000000000000000000110;
      data_mem[7] = 32'b1000000000000000000000000000111;
      data_mem[8] = 32'b0100000000000000000000000000110;
      data_mem[9] = 32'b0100000000000000000000000000111;
      data_mem[10] = 32'b0100000000000000000000000000110;
      data_mem[11] = 32'b1000000000000000000000000000111;
      data_mem[12] = 32'b0100000000000000000000000000110;
      data_mem[13] = 32'b1000000000000000000000000000111;
      data_mem[14] = 32'b1000000000000000000000000000110;
    end

    // Data memory and control logic
    always @(posedge clk, posedge rst) begin
        if (rst) begin
            ans1 <= 0;
        end 
    end
  always@(*)begin
    case(ForwardBE)
			2'b00:datain=in2_2;
			2'b10:datain=out;
		endcase	
      end
    always @(posedge clk, posedge rst) begin
        begin
          if (memread_2) begin
                // Read operation
          ans1 <= data_mem[address];
            end
          else if (memwrite_2) begin
                // Write operation
          data_mem[address] <= datain;
            end
      end
    end
endmodule

module OUTPUT(clk,rst,memtoreg,ans,ans1,out);
  input clk,rst;
  input memtoreg;           
  input [31:0] ans,ans1;          //ans from ALU operation and ans1 from lw
            
  output reg [31:0] out;          // output we got at the end
    
  always@(*)
     begin
       if (memtoreg)           // checking what to come in output, either from memory or from ALU
         out=ans1;                // output from memory
       else
         out=ans;                 // output from ALU
      end
        
 endmodule   


module CONTROL(
  input [5:0] opcode,
  output reg regdst,
  output reg alusrc,
  output reg memtoreg,
  output reg regwrite,
  output reg memread,
  output reg memwrite,
  output reg branch,
  output reg [1:0] aluop,
  output reg jump
);
  

  always @(*) begin
    case(opcode)
      6'b000000: begin // R - type
        regdst = 1'b1;
        alusrc = 1'b0;
        memtoreg = 1'b0;
        regwrite = 1'b1;
        memread = 1'b0;
        memwrite = 1'b0;
        branch = 1'b0;
        aluop = 2'b10;
        jump = 1'b0;
      end
      6'b100011: begin // lw - load word
        regdst = 1'b0;
        alusrc = 1'b1;
        memtoreg = 1'b1;
        regwrite = 1'b1;
        memread = 1'b1;
        memwrite = 1'b0;
        branch = 1'b0;
        aluop = 2'b00;
        jump = 1'b0;
      end
      6'b101011: begin // sw - store word
        regdst = 1'bx;
        alusrc = 1'b1;
        memtoreg = 1'bx;
        regwrite = 1'b0;
        memread = 1'b0;
        memwrite = 1'b1;
        branch = 1'b0;
        aluop = 2'b00;
        jump = 1'b0;
      end
      6'b000101: begin // bne - branch if not equal
        regdst = 1'b0;
        alusrc = 1'b0;
        memtoreg = 1'b0;
        regwrite = 1'b0;
        memread = 1'b0;
        memwrite = 1'b0;
        branch = 1'b1;
        aluop = 2'b01;
        jump = 1'b0;
      end
      6'b001110: begin // XORI - XOR immediate
        regdst = 1'b0;
        alusrc = 1'b1;
        memtoreg = 1'b0;
        regwrite = 1'b1;
        memread = 1'b0;
        memwrite = 1'b0;
        branch = 1'b0;
        aluop = 2'b11;
        jump = 1'b0;
      end
      6'b000010: begin // j - Jump
        regdst = 1'b0;
        alusrc = 1'b0;
        memtoreg = 1'b0;
        regwrite = 1'b0;
        memread = 1'b0;
        memwrite = 1'b0;
        branch = 1'b0;
        aluop = 2'b00;
        jump = 1'b1;
      end
      default: begin
        regdst = 1'b0;
        alusrc = 1'b0;
        memtoreg = 1'b0;
        regwrite = 1'b0;
        memread = 1'b0;
        memwrite = 1'b0;
        branch = 1'b0;
        aluop = 2'b10;
        jump = 1'b0;
      end
    endcase
  end
endmodule

module FORWARDINGUNIT (
    input [4:0] id_ex_rs, id_ex_rt, ex_mem_rd, mem_wb_rd,
    input ex_mem_regwrite, mem_wb_regwrite,clk,
    output reg [1:0] ForwardA, ForwardB
);

initial begin
    ForwardA = 2'b00;
    ForwardB = 2'b00;
end

  always @(posedge clk) begin
    if (ex_mem_regwrite && (ex_mem_rd != 5'b0) && (ex_mem_rd == id_ex_rs))
        ForwardA = 2'b10;//forwarding from EX/MEM stage
    else if (mem_wb_regwrite && (mem_wb_rd != 5'b0) && (mem_wb_rd == id_ex_rs))
      ForwardA = 2'b01; //forwarding from MEM/WB stage
    else
        ForwardA = 2'b00;
    
    if (ex_mem_regwrite && (ex_mem_rd != 5'b0) && (ex_mem_rd == id_ex_rt))
        ForwardB = 2'b10;
    else if (mem_wb_regwrite && (mem_wb_rd != 5'b0) && (mem_wb_rd == id_ex_rt))
        ForwardB = 2'b01;
    else
        ForwardB = 2'b00;
end

endmodule

module StallControl (
    input memread_1,clk,
  input [4:0] rt_1,rs,rt,
    output reg pcwrite, if_id_write, id_ex_flush);

  always @ (memread_1 or rt_1 or rs or rt or posedge clk)
    begin

        // If the instruction is a load (needs data memory)and if the destination register field of the load in 
        // the EX stage matches either source register of the instruction in the ID stage - STALL
        if(memread_1 & ((rt_1 == rs) | (rt_1 == rt)))
        begin 
            pcwrite <= 0;           // if instruction in the ID stage is stalled, then the instruction in the IF stage must also be stalled
            if_id_write <= 0;       // otherwise, we would lose the fetched instruction - set PCWrite as well as IF/IDwrite to 0  
            id_ex_flush <= 1; // for stalling in ID stage
        end

        else 
        begin 
            pcwrite <= 1;
            if_id_write <= 1;
            id_ex_flush<=0; 
        end

    end
endmodule

module determine_jump_or_branch (
    input jump, branch,clk, 
    input [31:0] branch_addr, jump_addr,
    output reg pcsrc,
    output reg [31:0] addr_out);

  always @(jump or branch or branch_addr or jump_addr or posedge clk)
    begin

        // If Branch is set, set branch_addr as the next instruction address
        // PCSrc is 1
      if (branch == 1)
        begin 
            addr_out <= branch_addr;
            pcsrc <= 1; 
        end

        // If Jump is set, set jump_addr as the next instruction address
        // PCSrc is 1
      else if (jump == 1)
        begin 
            addr_out <= jump_addr;
            pcsrc <= 1;
        end

	// Else PCSrc is set to 0, addr_out does not matter as next instruction address is simply PC + 4
        else 
            begin 
                pcsrc <= 0; 
                addr_out <= 32'b0; 
            end
	end
endmodule

module SW_forwarding_unit(
	input forwarding,
	input regwrite_2,
	input memwrite_1,
  input [4:0] rd_3,
  input [4:0] rd_2,
  output reg [1:0] ForwardBE
);

	always @(*) begin
		// Default values for forwarding signals
		ForwardBE = 2'b00;
		
		if (forwarding) begin
			// Forwarding for BE path (Write data to memory)
			if (regwrite_2 && memwrite_1 && (rd_3 != 5'b00000) && (rd_3 == rd_2))
			ForwardBE = 2'b10;
		
			end
	end

endmodule

module branch_and_jump_hazard_unit (
    input pcsrc,clk, 
    output reg if_id_flush, id_flush_branch, ex_mem_flush);

  always @(pcsrc or posedge clk)
    begin
        if(pcsrc)
        begin 
            if_id_flush <= 1;      
            id_flush_branch <=1; 
            ex_mem_flush <=1; 
        end

        else 
        begin 
            if_id_flush <= 0; 
            id_flush_branch <= 0; 
            ex_mem_flush <= 0; 
        end
    end 
endmodule
module counter_n #(parameter BITS = 32) (
    input clk1,
    input rst,
    output reg [BITS - 1:0] q
);

    // Initialize the counter register
    always @ (posedge clk1, posedge rst) begin
        if (rst) begin
            q <= 0;
        end else begin
            q <= q + 1;
        end
    end

endmodule

// seven-segment digit display driver
module sseg_display (
    input [3:0] hex,
    output reg [6:0] seg
    );
     
    // activate on any input change
    always @*
    begin
        case(hex)
            4'h0: seg[6:0] = 7'b1000000;    // digit 0
            4'h1: seg[6:0] = 7'b1111001;    // digit 1
            4'h2: seg[6:0] = 7'b0100100;    // digit 2
            4'h3: seg[6:0] = 7'b0110000;    // digit 3
            4'h4: seg[6:0] = 7'b0011001;    // digit 4
            4'h5: seg[6:0] = 7'b0010010;    // digit 5
            4'h6: seg[6:0] = 7'b0000010;    // digit 6
            4'h7: seg[6:0] = 7'b1111000;    // digit 7
            4'h8: seg[6:0] = 7'b0000000;    // digit 8
            4'h9: seg[6:0] = 7'b0010000;    // digit 9
            4'ha: seg[6:0] = 7'b0001000;    // digit A
            4'hb: seg[6:0] = 7'b0000011;    // digit B
            4'hc: seg[6:0] = 7'b1000110;    // digit C
            4'hd: seg[6:0] = 7'b0100001;    // digit D
            4'he: seg[6:0] = 7'b0000110;    // digit E
            default: seg[6:0] = 7'b0001110; // digit F
        endcase
    end
endmodule

module sevensegment(
    input clk1,
	  input sw,
    input [31:0] out,
  output [6:0] seg,
    output [3:0] an
    );
  
    reg [3:0] sw1,sw2,sw3,sw4;
    wire [6:0] seg0, seg1, seg2, seg3;
  
  //coverting the 16-bit input into 4 4-bits number   
    // Slice the input number into four 4-bit segments
	 always@(*) begin
	 case(sw)
	 1'b0: begin
     sw1 = out[3:0];
     sw2 = out[7:4];
     sw3 = out[11:8];
     sw4 = out[15:12];
	 end
	 1'b1: begin
	    sw1 = out[19:16];
       sw2 = out[23:20];
       sw3 = out[27:24];
       sw4 = out[31:28];
     	 end
	 endcase
	 end

  //converting the 4-bit number to display it on seven segment display
  sseg_display s0(.hex(sw1), .seg(seg0));     
  sseg_display s1(.hex(sw2), .seg(seg1));     
  sseg_display s2(.hex(sw3), .seg(seg2));     
  sseg_display s3(.hex(sw4), .seg(seg3));     
 
  //callinng the module tp display the number on fpga
    sseg_mux display(.clk1(clk1), .rst(1'b0), .dig0(seg0), .dig1(seg1), .dig2(seg2), .dig3(seg3), .an(an), .sseg(seg));
endmodule

//oing the time multiplexing on our output
module sseg_mux(
    input clk1, rst,
    input [6:0] dig0, dig1, dig2, dig3,
    output reg [3:0] an,
    output reg [6:0] sseg
    );
  
    // refresh rate of ~1526Hz (100 MHz / 2^16)
    localparam BITS = 18;
  wire [BITS - 1 : 0] q;
    counter_n #(.BITS(BITS)) counter(.clk1(clk1), .rst(rst), .q(q));
     
 
     
    always @*
      case (q[BITS - 1 : BITS - 2])
            2'b00:
                begin
                    an = 4'b1110;
                    sseg = dig0;
                end
            2'b01:
                begin
                    an = 4'b1101;
                    sseg = dig1;
                end
            2'b10:
                begin
                    an = 4'b1011;
                    sseg = dig2;
                end
            default:
                begin
                    an = 4'b0111;
                    sseg = dig3;
                end
        endcase                         
endmodule

module toplevel(
input clk,
input clk1,
  input sw,
    input rst,
  output[3:0] an,
  output[6:0] seg

);
    // Declare internal wires for module connections
  wire[5:0] opcode,funct;
  wire [31:0] pcout,pcin,instr,pcout1,instr1,immdata,constant,constant1;
  wire if_id_write;
  wire[3:0] alucontrol;
  wire[4:0] rs,rt,rd,shamt,rs_1,rt_1,rd_1,rd_2,rd_3;
  wire[31:0] in1,in2,dest,in1_1,in2_1,in2_2,in1out,in2out;
  wire[31:0] ans,ans_1,ans_2,ans1;
  wire regdest,memtoreg,alusrc,regdst,jump,branch,memread,memwrite,regwrite,regwrite_1, branch_1,jump_1, alusrc_1, memread_1, memwrite_1, memtoreg_1, memtoreg_2, memwrite_2, memread_2, regwrite_2, branch_2,jump_2,regwrite_3, memtoreg_3;
  wire[1:0] aluop;
  wire if_id_flush,ex_mem_flush,id_ex_flush,id_flush_branch;
  wire [31:0] ALUmuxoutput1,ALUmuxoutput2;
  wire ForwardA,ForwardB;
  wire zero,Less;
  wire id_regdest,id_memtoreg,id_alusrc,id_regdst,id_branch,id_memread,id_memwrite;
  wire[31:0] address,jump_addr,jump_addr_1,branch_addr,branch_addr_1;
  wire forwarding=1'b1;
    // Instantiate the PC module
    PC pc_inst (
      .pcin(pcin),
        .clk(clk),
        .rst(rst),
        .pcwrite(pcwrite),
      .pcout(pcout)
    );
  ADDER pc_add(
    .a(pcout),
    .b(32'b1),
    .c(pcin)
  );

  // Instantiate the ROM module
    ROM rom_inst (
        .clk(clk),
        .rst(rst),
        .pcout(pcout),
        .instr(instr)
    );

IF_ID_reg if_id_reg_inst (
        .pcout(pcout),
        .instr(instr),
        .clk(clk),
        .rst(rst),
      .if_id_write(if_id_write),
      .if_id_flush(if_id_flush), 
        .pcout1(pcout1),
      .instr1(instr1)
    );
    

    // Instantiate the control unit
    CONTROL control_inst (
        .opcode(opcode),
        .regdst(regdst),
        .alusrc(alusrc),
        .memtoreg(memtoreg),
        .regwrite(regwrite),
        .memread(memread),
        .memwrite(memwrite),
        .branch(branch),
        .aluop(aluop),
      .jump(jump)
    );
   // Instantiate the decoder
    DECODER decoder_inst (
        .instr(instr1),
        .rd(rd),
        .rs(rs),
        .rt(rt),
        .shamt(shamt),
        .opcode(opcode),
      .funct(funct),
      .immdata(immdata)
    );
  
    // Instantiate the register file
    REGFILE regfile_inst (
        .clk(clk),
        .rst(rst),
        .regwrite(regwrite),
        .regdest(regdst),
        .rs(rs),
        .rt(rt),
        .rd(rd),
        .ans(ans),
        .in1(in1),
      .in2(in2),
       .dest(dest)
    );
  

    // Instantiate the sign extend module
    sign_extend sign_extend_inst (
        .instr(instr1),
      .immdata(immdata),
      .pcout1(pcout1),
      .opcode(opcode),
      .rs(rs),
      .constant(constant),
      .jump_addr(jump_addr)
    );
    // Instantiate the ID/EX register
    ID_EX_reg id_ex_reg_inst (
      .adr(adr),
        .pcout1(pcout1),
        .in1(in1),
      .in2(in2),
        .constant(constant),
        .alucontrol(alucontrol),
        .rs(rs),
        .rt(rt),
        .rd(rd),
        .regwrite(regwrite),
        .branch(branch),
       .jump(jump),
        .alusrc(alusrc),
        .memread(memread),
        .memwrite(memwrite),
        .memtoreg(memtoreg),
        .clk(clk),
        .rst(rst),
      .id_ex_flush(id_ex_flush),
      .id_flush_branch(id_flush_branch),
        .aluop(aluop),
      .adr1(adr1),
        .pcout2(pcout2),
        .in1_1(in1_1),
        .in2_1(in2_1),
        .constant1(constant1),
        .alucontrol_1(alucontrol_1),
        .rs_1(rs_1),
        .rt_1(rt_1),
        .rd_1(rd_1),
        .regwrite_1(regwrite_1),
        .branch_1(branch_1),
      .jump_1(jump_1),
        .alusrc_1(alusrc_1),
        .memread_1(memread_1),
        .memwrite_1(memwrite_1),
        .memtoreg_1(memtoreg_1),
        .aluop_1(aluop_1)
    );
  
   // Instantiate the Forwarding Unit
    FORWARDINGUNIT f1 (
        .id_ex_rs(rs_1),
        .id_ex_rt(rt_1),
        .ex_mem_rd(rd_2),
        .mem_wb_rd(rd_3),
        .ex_mem_regwrite(regwrite_2),
      .mem_wb_regwrite(regwrite_3),
      .clk(clk),
        .ForwardA(ForwardA),
        .ForwardB(ForwardB)
    );
  
   // Instantiate the ALU control unit
    ALUCONTROL alucontrol_inst (
        .funct(funct),
      .aluop(aluop_1),
        .alucontrol(alucontrol)
    );
  
     // Instantiate the ALU
    ALU alu_inst (
      .clk(clk),
        .in1_1(in1_1),
      .in2_1(in2_1),
        .constant1(constant1),
      .out(out),
      .alusrc(alusrc_1),
        .alucontrol(alucontrol_1),
        .zero(zero),
      .Less(Less),
      .ans(ans),
      .ans_1(ans_1)
    );
  
  ADDER add(.a(pcout2),.b(constant1),.c(branch_addr));

    // Instantiate the EX/MEM register
    EX_MEM_reg ex_mem_reg_inst (
      .pcout2(pcout2),
      .adr1(adr1),
        .branch_addr(branch_addr),
      .jump_addr(jump_addr),
        .ans(ans),
      .in2_1(in2_1),
        .rd_1(rd_1),
        .memtoreg_1(memtoreg_1),
        .memwrite_1(memwrite_1),
        .memread_1(memread_1),
        .regwrite_1(regwrite_1),
        .clk(clk),
        .branch_1(branch_1),
        .jump_1(jump_1),
        .rst(rst),
      .ex_mem_flush(ex_mem_flush), 
      .branch_addr_1(branch_addr_1),
      .jump_addr_1(jump_addr_1),
        .ans_1(ans_1),
      .in2_2(in2_2),
        .rd_2(rd_2),
        .memtoreg_2(memtoreg_2),
        .memwrite_2(memwrite_2),
        .memread_2(memread_2),
        .regwrite_2(regwrite_2),
      .branch_2(branch_2),
      .jump_2(jump_2),
      .pcout3(pcout3),
      .adr2(adr2)
    );
   // Instantiate the data memory
    DATA_MEMORY data_memory_inst (
      .address(ans_1), 
      .ans1(ans1), 
    .clk(clk), 
      .memwrite_2(memwrite_2),
    .rst(rst),
      .memread_2(memread_2),
      .in2_2(in2_2),
      .out(out),
      .ForwardBE(ForwardBE)
);
  
 determine_jump_or_branch jorb(
   .clk(clk),
   .jump(jump),
   .branch(branch_2), 
   .branch_addr(branch_addr_1),
   .jump_addr(jump_addr_1),
   .pcsrc(pcsrc),
   .addr_out(addr_out));
 
  SW_forwarding_unit sw_forward (
	 .forwarding(forwarding),
       .regwrite_2(regwrite_2), 
       .memwrite_1(memwrite_1), 
       .rd_3(rd_3), 
       .rd_2(rd_2), 
    .ForwardBE(ForwardBE)
    );


    // Instantiate the MEM/WB register
    MEM_WB_reg mem_wb_reg_inst (
        .pcsrc(pcsrc),
      .ans_1(ans_1),
        .regwrite_2(regwrite_2),
        .memtoreg_2(memtoreg_2),
        .clk(clk),
        .rst(rst),
        .rd_2(rd_2),
      .pcsrc_1(pcsrc_1),
      .ans_2(ans_2),
        .regwrite_3(regwrite_3),
        .memtoreg_3(memtoreg_3),
        .rd_3(rd_3)
    );
 
   // Instantiate the output module
    OUTPUT output_inst (
        .clk(clk),
        .rst(rst),
      .memtoreg(memtoreg_3),
        .ans(ans),
      .ans1(ans1),
      .out(out)
    );
  

 branch_and_jump_hazard_unit borj_hazard(
   .clk(clk),
   .pcsrc(pcsrc_1),
   .if_id_flush(if_id_flush),
   .id_flush_branch(id_flush_branch),
   .ex_mem_flush(ex_mem_flush)
);
  
 StallControl stall(
  .clk(clk),
  .pcwrite(pcwrite),
  .if_id_write(if_id_write),
  .id_ex_flush(id_ex_flush),
  .memread_1(memread_1),
  .rt_1(rt_1),
  .rs(rs),
  .rt(rt)
);
 sevensegment segdis(
   .clk1(clk1),
   .sw(sw),
   .out(out),
   .seg(seg),
   .an(an)
 );


endmodule


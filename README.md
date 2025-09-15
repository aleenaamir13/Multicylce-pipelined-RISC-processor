# Multicylce-pipelined-RISC-processor
This project designs and implements a MIPS processor in Verilog HDL with a 5-stage pipeline (IF, ID, EX, MEM, WB). It supports R, I, and J instructions, load/store (lw, sw), branch (beq), and jump (j). Forwarding and hazard detection units manage data/control hazards, enabling correct execution with dependencies and hazards.

# Features
5-Stage Pipeline: IF, ID, EX, MEM, WB
Instruction Support:
R-type, I-type, J-type
Load/Store: lw, sw
Branch: beq
Jump: j
Forwarding Unit: Handles data hazards efficiently
Hazard Detection Unit: Resolves control hazards and stalls when necessary
Executes instructions with and without hazards

# Architecture
Instruction Fetch (IF): Fetches instructions from memory.
Instruction Decode (ID): Decodes instructions, reads registers.
Execute (EX): Performs ALU operations and address calculations.
Memory (MEM): Handles load/store instructions.
Write Back (WB): Writes results back to registers.

# Requirements
Verilog HDL,
Simulation/FPGA Tools: Xilinx ISE Design suite,
Testbench for instruction execution and hazard testing

# Usage
Modify the instruction memory file to test different programs.
Run simulation to check pipeline stages, hazards, and forwarding.
Observe waveforms to verify correct execution.

# Results
Successfully executes R, I, and J instructions.
Handles load/store, branch, and jump operations.
Demonstrates correct hazard handling with forwarding and stalling.

# Output Video on FPGA link
https://drive.google.com/drive/folders/1-VahC2TCFnzjOyLHs5lxR0_2RUMRoy0B

# Output R type instruction
<img width="1125" height="485" alt="image" src="https://github.com/user-attachments/assets/cc7882fa-0b27-475d-b5c9-10526d2917c7" />

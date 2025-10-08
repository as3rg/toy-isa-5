class TOYISA5Assembler
  def initialize
    @instructions = []
  end

  def proc(&block)
    instance_eval(&block) if block_given?
    self
  end

  def nor(rd, rs, rt)
    # 000000 | rs | rt | rd | 00000 | 001101
    instruction = (0b000000 << 26) | (rs << 21) | (rt << 16) | (rd << 11) | (0b00000 << 6) | 0b001101
    @instructions << instruction
    instruction
  end

  def ldp(rt1, rt2, base, offset)
    # 111100 | base | rt1 | rt2 | offset[10:0]
    # offset must have lowest 2 bits as 0
    raise "Misaligned offset: #{offset}" unless (offset & 0b11).zero?
    instruction = (0b111100 << 26) | (base << 21) | (rt1 << 16) | (rt2 << 11) | (offset & 0x7FF)
    @instructions << instruction
    instruction
  end

  def cbit(rd, rs, imm5)
    # 111001 | rd | rs | imm5 | 00000000000
    instruction = (0b111001 << 26) | (rd << 21) | (rs << 16) | (imm5 << 11) | 0b00000000000
    @instructions << instruction
    instruction
  end

  def bdep(rd, rs1, rs2)
    # 000000 | rd | rs1 | rs2 | 00000 | 110011
    instruction = (0b000000 << 26) | (rd << 21) | (rs1 << 16) | (rs2 << 11) | (0b00000 << 6) | 0b110011
    @instructions << instruction
    instruction
  end

  def add(rd, rs, rt)
    # 000000 | rs | rt | rd | 00000 | 011010
    instruction = (0b000000 << 26) | (rs << 21) | (rt << 16) | (rd << 11) | (0b00000 << 6) | 0b011010
    @instructions << instruction
    instruction
  end

  def ssat(rd, rs, imm5)
    # 001100 | rd | rs | imm5 | 00000000000
    instruction = (0b001100 << 26) | (rd << 21) | (rs << 16) | (imm5 << 11) | 0b00000000000
    @instructions << instruction
    instruction
  end

  def st(rt, base, offset)
    # 110010 | base | rt | offset[15:0]
    # offset must have lowest 2 bits as 0
    raise "Misaligned offset: #{offset}" unless (offset & 0b11).zero?
    instruction = (0b110010 << 26) | (base << 21) | (rt << 16) | (offset & 0xFFFF)
    @instructions << instruction
    instruction
  end

  def clz(rd, rs)
    # 000000 | rd | rs | 0000000000 | 110101
    instruction = (0b000000 << 26) | (rd << 21) | (rs << 16) | (0b0000000000 << 6) | 0b110101
    @instructions << instruction
    instruction
  end

  def bne(rs, rt, offset)
    # 000110 | rs | rt | offset[15:0]
    instruction = (0b000110 << 26) | (rs << 21) | (rt << 16) | (offset & 0xFFFF)
    @instructions << instruction
    instruction
  end

  def ld(rt, base, offset)
    # 001010 | base | rt | offset[15:0]
    # offset must have lowest 2 bits as 0
    raise "Misaligned offset: #{offset}" unless (offset & 0b11).zero?
    instruction = (0b001010 << 26) | (base << 21) | (rt << 16) | (offset & 0xFFFF)
    @instructions << instruction
    instruction
  end

  def xor(rd, rs, rt)
    # 000000 | rs | rt | rd | 00000 | 101001
    instruction = (0b000000 << 26) | (rs << 21) | (rt << 16) | (rd << 11) | (0b00000 << 6) | 0b101001
    @instructions << instruction
    instruction
  end

  def syscall(code = 0)
    # 000000 | code[19:0] | 111000
    instruction = (0b000000 << 26) | ((code & 0xFFFFF) << 6) | 0b111000
    @instructions << instruction
    instruction
  end

  def beq(rs, rt, offset)
    # 011110 | rs | rt | offset[15:0]
    instruction = (0b011110 << 26) | (rs << 21) | (rt << 16) | (offset & 0xFFFF)
    @instructions << instruction
    instruction
  end

  def j(index)
    # 110110 | index[25:0]
    instruction = (0b110110 << 26) | (index & 0x3FFFFFF)
    @instructions << instruction
    instruction
  end

  def write_to_file(filename)
    File.open(filename, 'wb') do |file|
      @instructions.each do |instruction|
        # Write as 32-bit little-endian
        file.write([instruction].pack('V'))
      end
    end
    puts "Written #{@instructions.size} instructions to #{filename}"
  end

  def clear
    @instructions.clear
  end

  def instructions
    @instructions.dup
  end

  def to_binary(instruction)
    instruction.to_s(2).rjust(32, '0')
  end

  def to_hex(instruction)
    "0x#{instruction.to_s(16).rjust(8, '0')}"
  end

  def display
    puts "Generated instructions:"
    @instructions.each_with_index do |instr, i|
      puts "Instruction #{i}: #{to_binary(instr)} #{to_hex(instr)}"
    end
  end

  def r0
    0
  end

  def r1
    1
  end

  def r2
    2
  end

  def r3
    3
  end

  def r4
    4
  end

  def r5
    5
  end

  def r6
    6
  end

  def r7
    7
  end

  def r8
    8
  end

  def r9
    9
  end

  def r10
    10
  end

  def r11
    11
  end

  def r12
    12
  end

  def r13
    13
  end

  def r14
    14
  end

  def r15
    15
  end

  def r16
    16
  end

  def r17
    17
  end

  def r18
    18
  end

  def r19
    19
  end

  def r20
    20
  end

  def r21
    21
  end

  def r22
    22
  end

  def r23
    23
  end

  def r24
    24
  end

  def r25
    25
  end

  def r26
    26
  end

  def r27
    27
  end

  def r28
    28
  end

  def r29
    29
  end

  def r30
    30
  end

  def r31
    31
  end

  def li(reg, val)
    nor reg, reg, reg
    (0...32).step do |x|
      if (val & (1 << x)) == 0 then
        cbit reg, reg, x
      end
    end
  end

end

# Example usage:
if __FILE__ == $0
  assembler = TOYISA5Assembler.new

  assembler.proc do
    li r0, 0
    li r1, 1

    li r2, 0   # Fib[n - 1]
    li r3, 1   # Fib[n    ]

    li r4, 8   # n
    nor r5, r5, r5

    beq r4, r1, 6
    add r4, r4, r5

    add r6, r2, r0
    add r2, r3, r0
    add r3, r2, r6

    beq r0, r0, -5

    li r8, 60
    add r0, r0, r3

    syscall
  end

  # Display and save
  assembler.display
  assembler.write_to_file('program.bin')
end

#!/usr/bin/env ruby

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

  (0..31).each { |i| define_method("r#{i}") { i } }

  def li(reg, val)
    nor reg, reg, reg
    (0...32).step do |x|
      if (val & (1 << x)) == 0 then
        cbit reg, reg, x
      end
    end
  end

end

if ARGV.empty?
  puts "Usage: #{$0} <filename>"
  exit 1
end

filename = ARGV[0]

unless File.exist?(filename)
  puts "Error: File '#{filename}' not found"
  exit 1
end

begin
  assembler = TOYISA5Assembler.new
  content = File.read(filename)
  assembler.proc do
    eval(content)
  end
  assembler.display
  assembler.write_to_file('program.bin')
rescue SyntaxError => e
  puts "Syntax error in file: #{e.message}"
rescue SecurityError => e
  puts "Security error: #{e.message}"
rescue StandardError => e
  puts "Error during evaluation: #{e.message}"
end

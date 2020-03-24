# frozen_string_literal: true

require 'pathname'

desc 'generate AST graphs for all examples'
task :graphs do
  Pathname.glob("#{__dir__}/examples/*/*.mc").each do |mc|
    dot = mc.sub_ext('.dot')
    svg = mc.sub_ext('.svg')
    sh 'cargo', 'run', '--bin', 'mc_ast_to_dot', '--', '-o', dot.to_s, mc.to_s
    sh 'dot', '-T', 'svg', '-o', svg.to_s, dot.to_s

    begin
      sh 'sed', '-i', '', '-E', 's/\s*(height|width)="[^"]+"\s*/ /g', svg.to_s
      sh 'svgcleaner', svg.to_s, svg.to_s
      sh 'xmllint', '--format', svg.to_s, '-o', svg.to_s
    rescue RuntimeError
      # Ignore optional commands failing.
    end
  end
end

desc 'generate Symbol Tables for all examples'
task :symbol_tables do
  Pathname.glob("#{__dir__}/examples/*/*.mc").each do |mc|
    txt = mc.sub_ext('.txt')
    sh 'cargo', 'run', '--bin', 'mc_symbol_table', '--', '-o', txt.to_s, mc.to_s
  end
end

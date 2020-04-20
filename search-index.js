var searchIndex={};
searchIndex["mc_ast_to_dot"] = {"doc":"","i":[[5,"mc_ast_to_dot","mc_ast_to_dot","",null,[[],["result"]]],[0,"add_to_graph","","",null,null],[6,"AstGraph","mc_ast_to_dot::add_to_graph","",null,null],[8,"AddToGraph","","",null,null],[10,"add_to_graph","","",0,[[["self"],["graph"]],["nodeindex"]]]],"p":[[8,"AddToGraph"]]};
searchIndex["mc_ir"] = {"doc":"","i":[[5,"mc_ir","mc_ir","",null,[[],["result"]]],[0,"ir","","",null,null],[3,"IntermediateRepresentation","mc_ir::ir","",null,null],[12,"instructions","","",0,null],[12,"stack","","",0,null],[4,"Object","","",null,null],[13,"Variable","","",1,null],[13,"Literal","","",1,null],[13,"FunctionCall","","",1,null],[4,"Instruction","","",null,null],[13,"Assignment","","",2,null],[12,"des","mc_ir::ir::Instruction","",2,null],[12,"obj","","",2,null],[13,"BinaryAssignment","mc_ir::ir","",2,null],[12,"des","mc_ir::ir::Instruction","",2,null],[12,"obj1","","",2,null],[12,"op","","",2,null],[12,"obj2","","",2,null],[13,"UnaryAssignment","mc_ir::ir","",2,null],[12,"des","mc_ir::ir::Instruction","",2,null],[12,"op","","",2,null],[12,"obj","","",2,null],[8,"AddToIr","mc_ir::ir","",null,null],[11,"add_to_ir","","",3,[[["self"],["intermediaterepresentation"]]]],[11,"from","","",0,[[["t"]],["t"]]],[11,"into","","",0,[[],["u"]]],[11,"try_from","","",0,[[["u"]],["result"]]],[11,"try_into","","",0,[[],["result"]]],[11,"borrow","","",0,[[["self"]],["t"]]],[11,"borrow_mut","","",0,[[["self"]],["t"]]],[11,"type_id","","",0,[[["self"]],["typeid"]]],[11,"from","","",1,[[["t"]],["t"]]],[11,"into","","",1,[[],["u"]]],[11,"try_from","","",1,[[["u"]],["result"]]],[11,"try_into","","",1,[[],["result"]]],[11,"borrow","","",1,[[["self"]],["t"]]],[11,"borrow_mut","","",1,[[["self"]],["t"]]],[11,"type_id","","",1,[[["self"]],["typeid"]]],[11,"from","","",2,[[["t"]],["t"]]],[11,"into","","",2,[[],["u"]]],[11,"try_from","","",2,[[["u"]],["result"]]],[11,"try_into","","",2,[[],["result"]]],[11,"borrow","","",2,[[["self"]],["t"]]],[11,"borrow_mut","","",2,[[["self"]],["t"]]],[11,"type_id","","",2,[[["self"]],["typeid"]]],[11,"default","","",0,[[],["intermediaterepresentation"]]]],"p":[[3,"IntermediateRepresentation"],[4,"Object"],[4,"Instruction"],[8,"AddToIr"]]};
searchIndex["mc_parser"] = {"doc":"","i":[[3,"McParser","mc_parser","",null,null],[4,"Rule","","",null,null],[13,"EOI","","",0,null],[13,"WHITESPACE","","",0,null],[13,"identifier","","",0,null],[13,"COMMENT","","",0,null],[13,"ty","","",0,null],[13,"not","","",0,null],[13,"unary_minus","","",0,null],[13,"plus","","",0,null],[13,"minus","","",0,null],[13,"times","","",0,null],[13,"divide","","",0,null],[13,"lte","","",0,null],[13,"lt","","",0,null],[13,"gte","","",0,null],[13,"gt","","",0,null],[13,"land","","",0,null],[13,"lor","","",0,null],[13,"eq","","",0,null],[13,"neq","","",0,null],[13,"unary_operator","","",0,null],[13,"binary_operator","","",0,null],[13,"boolean","","",0,null],[13,"int","","",0,null],[13,"float","","",0,null],[13,"quote","","",0,null],[13,"string","","",0,null],[13,"inner","","",0,null],[13,"literal","","",0,null],[13,"declaration_type","","",0,null],[13,"declaration","","",0,null],[13,"assignment","","",0,null],[13,"unary_expression","","",0,null],[13,"par_expression","","",0,null],[13,"variable_expression","","",0,null],[13,"term","","",0,null],[13,"expression","","",0,null],[13,"statement","","",0,null],[13,"condition","","",0,null],[13,"if_stmt","","",0,null],[13,"while_stmt","","",0,null],[13,"ret_stmt","","",0,null],[13,"compound_stmt","","",0,null],[13,"function_def","","",0,null],[13,"parameters","","",0,null],[13,"call_expr","","",0,null],[13,"arguments","","",0,null],[13,"program","","",0,null],[5,"parse","","",null,[[["str"]],[["result",["program","conversionerror"]],["program"],["conversionerror",["string"]]]]],[0,"ast","","",null,null],[3,"Identifier","mc_parser::ast","",null,null],[12,"0","","",1,null],[3,"Parameter","","",null,null],[12,"ty","","",2,null],[12,"count","","",2,null],[12,"identifier","","",2,null],[12,"span","","",2,null],[3,"Assignment","","",null,null],[12,"identifier","","",3,null],[12,"index_expression","","",3,null],[12,"rvalue","","",3,null],[12,"span","","",3,null],[3,"Declaration","","",null,null],[12,"ty","","",4,null],[12,"count","","",4,null],[12,"identifier","","",4,null],[12,"span","","",4,null],[3,"IfStatement","","",null,null],[12,"condition","","",5,null],[12,"block","","",5,null],[12,"else_block","","",5,null],[12,"span","","",5,null],[3,"WhileStatement","","",null,null],[12,"condition","","",6,null],[12,"block","","",6,null],[12,"span","","",6,null],[3,"ReturnStatement","","",null,null],[12,"expression","","",7,null],[12,"span","","",7,null],[3,"CompoundStatement","","",null,null],[12,"statements","","",8,null],[12,"span","","",8,null],[3,"FunctionDeclaration","","",null,null],[12,"ty","","",9,null],[12,"identifier","","",9,null],[12,"parameters","","",9,null],[12,"body","","",9,null],[12,"span","","",9,null],[3,"Program","","",null,null],[12,"function_declarations","","",10,null],[12,"span","","",10,null],[4,"Ty","","",null,null],[13,"Bool","","",11,null],[13,"Int","","",11,null],[13,"Float","","",11,null],[13,"String","","",11,null],[4,"Literal","","",null,null],[13,"Bool","","",12,null],[13,"Int","","",12,null],[13,"Float","","",12,null],[13,"String","","",12,null],[4,"UnaryOp","","",null,null],[13,"Minus","","",13,null],[13,"Not","","",13,null],[4,"BinaryOp","","",null,null],[13,"Plus","","",14,null],[13,"Minus","","",14,null],[13,"Times","","",14,null],[13,"Divide","","",14,null],[13,"Eq","","",14,null],[13,"Neq","","",14,null],[13,"Lte","","",14,null],[13,"Lt","","",14,null],[13,"Gte","","",14,null],[13,"Gt","","",14,null],[13,"Land","","",14,null],[13,"Lor","","",14,null],[4,"Expression","","",null,null],[13,"Literal","","",15,null],[12,"literal","mc_parser::ast::Expression","",15,null],[12,"span","","",15,null],[13,"Variable","mc_parser::ast","",15,null],[12,"identifier","mc_parser::ast::Expression","",15,null],[12,"index_expression","","",15,null],[12,"span","","",15,null],[13,"FunctionCall","mc_parser::ast","",15,null],[12,"identifier","mc_parser::ast::Expression","",15,null],[12,"arguments","","",15,null],[12,"span","","",15,null],[13,"Unary","mc_parser::ast","",15,null],[12,"op","mc_parser::ast::Expression","",15,null],[12,"expression","","",15,null],[12,"span","","",15,null],[13,"Binary","mc_parser::ast","",15,null],[12,"op","mc_parser::ast::Expression","",15,null],[12,"lhs","","",15,null],[12,"rhs","","",15,null],[12,"span","","",15,null],[4,"Statement","mc_parser::ast","",null,null],[13,"If","","",16,null],[13,"While","","",16,null],[13,"Ret","","",16,null],[13,"Decl","","",16,null],[13,"Assignment","","",16,null],[13,"Expression","","",16,null],[13,"Compound","","",16,null],[5,"climber","","",null,[[],[["rule"],["precclimber",["rule"]]]]],[11,"consume","","",15,[[["rule"],["pair",["rule"]],["precclimber"]],[["result",["conversionerror"]],["conversionerror"]]]],[11,"get_span","","",15,[[["self"]],["span"]]],[17,"_PEST_GRAMMAR_McParser","mc_parser","",null,null],[11,"from","","",17,[[["t"]],["t"]]],[11,"into","","",17,[[],["u"]]],[11,"try_from","","",17,[[["u"]],["result"]]],[11,"try_into","","",17,[[],["result"]]],[11,"borrow","","",17,[[["self"]],["t"]]],[11,"borrow_mut","","",17,[[["self"]],["t"]]],[11,"type_id","","",17,[[["self"]],["typeid"]]],[11,"from","","",0,[[["t"]],["t"]]],[11,"into","","",0,[[],["u"]]],[11,"to_owned","","",0,[[["self"]],["t"]]],[11,"clone_into","","",0,[[["self"],["t"]]]],[11,"try_from","","",0,[[["u"]],["result"]]],[11,"try_into","","",0,[[],["result"]]],[11,"borrow","","",0,[[["self"]],["t"]]],[11,"borrow_mut","","",0,[[["self"]],["t"]]],[11,"type_id","","",0,[[["self"]],["typeid"]]],[11,"from","mc_parser::ast","",1,[[["t"]],["t"]]],[11,"into","","",1,[[],["u"]]],[11,"to_owned","","",1,[[["self"]],["t"]]],[11,"clone_into","","",1,[[["self"],["t"]]]],[11,"to_string","","",1,[[["self"]],["string"]]],[11,"try_from","","",1,[[["u"]],["result"]]],[11,"try_into","","",1,[[],["result"]]],[11,"borrow","","",1,[[["self"]],["t"]]],[11,"borrow_mut","","",1,[[["self"]],["t"]]],[11,"type_id","","",1,[[["self"]],["typeid"]]],[11,"from","","",2,[[["t"]],["t"]]],[11,"into","","",2,[[],["u"]]],[11,"try_from","","",2,[[["u"]],["result"]]],[11,"try_into","","",2,[[],["result"]]],[11,"borrow","","",2,[[["self"]],["t"]]],[11,"borrow_mut","","",2,[[["self"]],["t"]]],[11,"type_id","","",2,[[["self"]],["typeid"]]],[11,"from","","",3,[[["t"]],["t"]]],[11,"into","","",3,[[],["u"]]],[11,"try_from","","",3,[[["u"]],["result"]]],[11,"try_into","","",3,[[],["result"]]],[11,"borrow","","",3,[[["self"]],["t"]]],[11,"borrow_mut","","",3,[[["self"]],["t"]]],[11,"type_id","","",3,[[["self"]],["typeid"]]],[11,"from","","",4,[[["t"]],["t"]]],[11,"into","","",4,[[],["u"]]],[11,"try_from","","",4,[[["u"]],["result"]]],[11,"try_into","","",4,[[],["result"]]],[11,"borrow","","",4,[[["self"]],["t"]]],[11,"borrow_mut","","",4,[[["self"]],["t"]]],[11,"type_id","","",4,[[["self"]],["typeid"]]],[11,"from","","",5,[[["t"]],["t"]]],[11,"into","","",5,[[],["u"]]],[11,"try_from","","",5,[[["u"]],["result"]]],[11,"try_into","","",5,[[],["result"]]],[11,"borrow","","",5,[[["self"]],["t"]]],[11,"borrow_mut","","",5,[[["self"]],["t"]]],[11,"type_id","","",5,[[["self"]],["typeid"]]],[11,"from","","",6,[[["t"]],["t"]]],[11,"into","","",6,[[],["u"]]],[11,"try_from","","",6,[[["u"]],["result"]]],[11,"try_into","","",6,[[],["result"]]],[11,"borrow","","",6,[[["self"]],["t"]]],[11,"borrow_mut","","",6,[[["self"]],["t"]]],[11,"type_id","","",6,[[["self"]],["typeid"]]],[11,"from","","",7,[[["t"]],["t"]]],[11,"into","","",7,[[],["u"]]],[11,"try_from","","",7,[[["u"]],["result"]]],[11,"try_into","","",7,[[],["result"]]],[11,"borrow","","",7,[[["self"]],["t"]]],[11,"borrow_mut","","",7,[[["self"]],["t"]]],[11,"type_id","","",7,[[["self"]],["typeid"]]],[11,"from","","",8,[[["t"]],["t"]]],[11,"into","","",8,[[],["u"]]],[11,"try_from","","",8,[[["u"]],["result"]]],[11,"try_into","","",8,[[],["result"]]],[11,"borrow","","",8,[[["self"]],["t"]]],[11,"borrow_mut","","",8,[[["self"]],["t"]]],[11,"type_id","","",8,[[["self"]],["typeid"]]],[11,"from","","",9,[[["t"]],["t"]]],[11,"into","","",9,[[],["u"]]],[11,"try_from","","",9,[[["u"]],["result"]]],[11,"try_into","","",9,[[],["result"]]],[11,"borrow","","",9,[[["self"]],["t"]]],[11,"borrow_mut","","",9,[[["self"]],["t"]]],[11,"type_id","","",9,[[["self"]],["typeid"]]],[11,"from","","",10,[[["t"]],["t"]]],[11,"into","","",10,[[],["u"]]],[11,"try_from","","",10,[[["u"]],["result"]]],[11,"try_into","","",10,[[],["result"]]],[11,"borrow","","",10,[[["self"]],["t"]]],[11,"borrow_mut","","",10,[[["self"]],["t"]]],[11,"type_id","","",10,[[["self"]],["typeid"]]],[11,"from","","",11,[[["t"]],["t"]]],[11,"into","","",11,[[],["u"]]],[11,"to_owned","","",11,[[["self"]],["t"]]],[11,"clone_into","","",11,[[["self"],["t"]]]],[11,"to_string","","",11,[[["self"]],["string"]]],[11,"try_from","","",11,[[["u"]],["result"]]],[11,"try_into","","",11,[[],["result"]]],[11,"borrow","","",11,[[["self"]],["t"]]],[11,"borrow_mut","","",11,[[["self"]],["t"]]],[11,"type_id","","",11,[[["self"]],["typeid"]]],[11,"from","","",12,[[["t"]],["t"]]],[11,"into","","",12,[[],["u"]]],[11,"try_from","","",12,[[["u"]],["result"]]],[11,"try_into","","",12,[[],["result"]]],[11,"borrow","","",12,[[["self"]],["t"]]],[11,"borrow_mut","","",12,[[["self"]],["t"]]],[11,"type_id","","",12,[[["self"]],["typeid"]]],[11,"from","","",13,[[["t"]],["t"]]],[11,"into","","",13,[[],["u"]]],[11,"to_string","","",13,[[["self"]],["string"]]],[11,"try_from","","",13,[[["u"]],["result"]]],[11,"try_into","","",13,[[],["result"]]],[11,"borrow","","",13,[[["self"]],["t"]]],[11,"borrow_mut","","",13,[[["self"]],["t"]]],[11,"type_id","","",13,[[["self"]],["typeid"]]],[11,"from","","",14,[[["t"]],["t"]]],[11,"into","","",14,[[],["u"]]],[11,"to_string","","",14,[[["self"]],["string"]]],[11,"try_from","","",14,[[["u"]],["result"]]],[11,"try_into","","",14,[[],["result"]]],[11,"borrow","","",14,[[["self"]],["t"]]],[11,"borrow_mut","","",14,[[["self"]],["t"]]],[11,"type_id","","",14,[[["self"]],["typeid"]]],[11,"from","","",15,[[["t"]],["t"]]],[11,"into","","",15,[[],["u"]]],[11,"try_from","","",15,[[["u"]],["result"]]],[11,"try_into","","",15,[[],["result"]]],[11,"borrow","","",15,[[["self"]],["t"]]],[11,"borrow_mut","","",15,[[["self"]],["t"]]],[11,"type_id","","",15,[[["self"]],["typeid"]]],[11,"from","","",16,[[["t"]],["t"]]],[11,"into","","",16,[[],["u"]]],[11,"try_from","","",16,[[["u"]],["result"]]],[11,"try_into","","",16,[[],["result"]]],[11,"borrow","","",16,[[["self"]],["t"]]],[11,"borrow_mut","","",16,[[["self"]],["t"]]],[11,"type_id","","",16,[[["self"]],["typeid"]]],[11,"from","","",11,[[["literal"]],["ty"]]],[11,"from","","",1,[[["str"]],["self"]]],[11,"clone","","",11,[[["self"]],["ty"]]],[11,"clone","","",1,[[["self"]],["identifier"]]],[11,"clone","mc_parser","",0,[[["self"]],["rule"]]],[11,"cmp","","",0,[[["self"],["rule"]],["ordering"]]],[11,"eq","mc_parser::ast","",11,[[["self"],["ty"]],["bool"]]],[11,"eq","","",12,[[["literal"],["self"]],["bool"]]],[11,"ne","","",12,[[["literal"],["self"]],["bool"]]],[11,"eq","","",13,[[["unaryop"],["self"]],["bool"]]],[11,"eq","","",14,[[["binaryop"],["self"]],["bool"]]],[11,"eq","","",15,[[["expression"],["self"]],["bool"]]],[11,"ne","","",15,[[["expression"],["self"]],["bool"]]],[11,"eq","","",1,[[["self"],["identifier"]],["bool"]]],[11,"ne","","",1,[[["self"],["identifier"]],["bool"]]],[11,"eq","","",2,[[["self"],["parameter"]],["bool"]]],[11,"ne","","",2,[[["self"],["parameter"]],["bool"]]],[11,"eq","","",3,[[["self"],["assignment"]],["bool"]]],[11,"ne","","",3,[[["self"],["assignment"]],["bool"]]],[11,"eq","","",4,[[["self"],["declaration"]],["bool"]]],[11,"ne","","",4,[[["self"],["declaration"]],["bool"]]],[11,"eq","","",5,[[["ifstatement"],["self"]],["bool"]]],[11,"ne","","",5,[[["ifstatement"],["self"]],["bool"]]],[11,"eq","","",6,[[["whilestatement"],["self"]],["bool"]]],[11,"ne","","",6,[[["whilestatement"],["self"]],["bool"]]],[11,"eq","","",7,[[["returnstatement"],["self"]],["bool"]]],[11,"ne","","",7,[[["returnstatement"],["self"]],["bool"]]],[11,"eq","","",8,[[["compoundstatement"],["self"]],["bool"]]],[11,"ne","","",8,[[["compoundstatement"],["self"]],["bool"]]],[11,"eq","","",16,[[["statement"],["self"]],["bool"]]],[11,"ne","","",16,[[["statement"],["self"]],["bool"]]],[11,"eq","","",9,[[["self"],["functiondeclaration"]],["bool"]]],[11,"ne","","",9,[[["self"],["functiondeclaration"]],["bool"]]],[11,"eq","","",10,[[["program"],["self"]],["bool"]]],[11,"ne","","",10,[[["program"],["self"]],["bool"]]],[11,"eq","mc_parser","",0,[[["self"],["rule"]],["bool"]]],[11,"partial_cmp","","",0,[[["self"],["rule"]],[["ordering"],["option",["ordering"]]]]],[11,"fmt","mc_parser::ast","",11,[[["formatter"],["self"]],["result"]]],[11,"fmt","","",12,[[["formatter"],["self"]],["result"]]],[11,"fmt","","",13,[[["formatter"],["self"]],["result"]]],[11,"fmt","","",14,[[["formatter"],["self"]],["result"]]],[11,"fmt","","",15,[[["formatter"],["self"]],["result"]]],[11,"fmt","","",1,[[["formatter"],["self"]],["result"]]],[11,"fmt","","",2,[[["formatter"],["self"]],["result"]]],[11,"fmt","","",3,[[["formatter"],["self"]],["result"]]],[11,"fmt","","",4,[[["formatter"],["self"]],["result"]]],[11,"fmt","","",5,[[["formatter"],["self"]],["result"]]],[11,"fmt","","",6,[[["formatter"],["self"]],["result"]]],[11,"fmt","","",7,[[["formatter"],["self"]],["result"]]],[11,"fmt","","",8,[[["formatter"],["self"]],["result"]]],[11,"fmt","","",16,[[["formatter"],["self"]],["result"]]],[11,"fmt","","",9,[[["formatter"],["self"]],["result"]]],[11,"fmt","","",10,[[["formatter"],["self"]],["result"]]],[11,"fmt","mc_parser","",0,[[["formatter"],["self"]],["result"]]],[11,"fmt","","",17,[[["formatter"],["self"]],["result"]]],[11,"fmt","mc_parser::ast","",11,[[["formatter"],["self"]],["result"]]],[11,"fmt","","",13,[[["formatter"],["self"]],["result"]]],[11,"fmt","","",14,[[["formatter"],["self"]],["result"]]],[11,"fmt","","",1,[[["formatter"],["self"]],["result"]]],[11,"hash","","",1,[[["self"],["__h"]]]],[11,"hash","mc_parser","",0,[[["self"],["__h"]]]],[11,"try_from","mc_parser::ast","",15,[[["str"]],["result"]]],[11,"try_from","","",2,[[["str"]],["result"]]],[11,"try_from","","",3,[[["str"]],["result"]]],[11,"try_from","","",4,[[["str"]],["result"]]],[11,"try_from","","",5,[[["str"]],["result"]]],[11,"try_from","","",6,[[["str"]],["result"]]],[11,"try_from","","",7,[[["str"]],["result"]]],[11,"try_from","","",8,[[["str"]],["result"]]],[11,"try_from","","",16,[[["str"]],["result"]]],[11,"try_from","","",9,[[["str"]],["result"]]],[11,"try_from","","",10,[[["str"]],["result"]]],[11,"from_pest","","",11,[[["pairs"]],[["conversionerror"],["result",["conversionerror"]]]]],[11,"from_pest","","",12,[[["pairs"]],[["conversionerror"],["result",["conversionerror"]]]]],[11,"from_pest","","",13,[[["pairs"]],[["conversionerror"],["result",["conversionerror"]]]]],[11,"from_pest","","",14,[[["pairs"]],[["conversionerror"],["result",["conversionerror"]]]]],[11,"from_pest","","",15,[[["pairs"]],[["conversionerror"],["result",["conversionerror"]]]]],[11,"from_pest","","",1,[[["pairs"]],[["conversionerror"],["result",["conversionerror"]]]]],[11,"from_pest","","",2,[[["pairs"]],[["conversionerror"],["result",["conversionerror"]]]]],[11,"from_pest","","",3,[[["pairs"]],[["conversionerror"],["result",["conversionerror"]]]]],[11,"from_pest","","",4,[[["pairs"]],[["conversionerror"],["result",["conversionerror"]]]]],[11,"from_pest","","",5,[[["pairs"]],[["conversionerror"],["result",["conversionerror"]]]]],[11,"from_pest","","",6,[[["pairs"]],[["conversionerror"],["result",["conversionerror"]]]]],[11,"from_pest","","",7,[[["pairs"]],[["conversionerror"],["result",["conversionerror"]]]]],[11,"from_pest","","",8,[[["pairs"]],[["conversionerror"],["result",["conversionerror"]]]]],[11,"from_pest","","",16,[[["pairs"]],[["conversionerror"],["result",["conversionerror"]]]]],[11,"from_pest","","",9,[[["pairs"]],[["conversionerror"],["result",["conversionerror"]]]]],[11,"from_pest","","",10,[[["pairs"]],[["conversionerror"],["result",["conversionerror"]]]]],[11,"parse","mc_parser","",17,[[["str"],["rule"]],[["pairs",["rule"]],["error",["rule"]],["result",["pairs","error"]]]]]],"p":[[4,"Rule"],[3,"Identifier"],[3,"Parameter"],[3,"Assignment"],[3,"Declaration"],[3,"IfStatement"],[3,"WhileStatement"],[3,"ReturnStatement"],[3,"CompoundStatement"],[3,"FunctionDeclaration"],[3,"Program"],[4,"Ty"],[4,"Literal"],[4,"UnaryOp"],[4,"BinaryOp"],[4,"Expression"],[4,"Statement"],[3,"McParser"]]};
searchIndex["mc_symbol_table"] = {"doc":"","i":[[5,"mc_symbol_table","mc_symbol_table","",null,[[],["result"]]],[0,"format_symbol_table","","",null,null],[0,"symbol_table","","",null,null],[3,"Scope","mc_symbol_table::symbol_table","",null,null],[12,"name","","",0,null],[12,"parent","","",0,null],[12,"symbols","","",0,null],[12,"return_type","","",0,null],[12,"children","","",0,null],[3,"SymbolTable","","",null,null],[12,"table","","",1,null],[4,"Symbol","","",null,null],[13,"Function","","",2,null],[13,"Variable","","",2,null],[11,"new","","",0,[[],[["refcell"],["rc",["refcell"]]]]],[11,"new_child","","",0,[[["str"],["rc"]],[["refcell"],["rc",["refcell"]]]]],[11,"insert","","",0,[[["self"],["identifier"],["symbol"]]]],[11,"lookup","","",0,[[["rc"],["identifier"]],[["option",["symbol"]],["symbol"]]]],[11,"lookup_in_scope","","",0,[[["rc"],["identifier"]],[["option",["symbol"]],["symbol"]]]],[11,"return_type","","",0,[[["rc"]],[["option",["ty"]],["ty"]]]],[0,"add_to_scope","mc_symbol_table","",null,null],[8,"AddToScope","mc_symbol_table::add_to_scope","",null,null],[10,"add_to_scope","","",3,[[["self"],["rc"]],[["result",["vec"]],["vec",["semanticerror"]]]]],[0,"semantic_error","mc_symbol_table","",null,null],[4,"SemanticError","mc_symbol_table::semantic_error","",null,null],[13,"Type","","",4,null],[12,"span","mc_symbol_table::semantic_error::SemanticError","",4,null],[12,"expected","","",4,null],[12,"actual","","",4,null],[13,"NotDeclared","mc_symbol_table::semantic_error","",4,null],[12,"span","mc_symbol_table::semantic_error::SemanticError","",4,null],[12,"identifier","","",4,null],[13,"AlreadyDeclared","mc_symbol_table::semantic_error","",4,null],[12,"span","mc_symbol_table::semantic_error::SemanticError","",4,null],[12,"identifier","","",4,null],[13,"ArrayError","mc_symbol_table::semantic_error","",4,null],[12,"span","mc_symbol_table::semantic_error::SemanticError","",4,null],[12,"identifier","","",4,null],[13,"IndexOutOfBounds","mc_symbol_table::semantic_error","",4,null],[12,"span","mc_symbol_table::semantic_error::SemanticError","",4,null],[12,"identifier","","",4,null],[12,"size","","",4,null],[12,"actual","","",4,null],[13,"WrongUseOfFunction","mc_symbol_table::semantic_error","",4,null],[12,"span","mc_symbol_table::semantic_error::SemanticError","",4,null],[12,"identifier","","",4,null],[13,"NotAFunction","mc_symbol_table::semantic_error","",4,null],[12,"span","mc_symbol_table::semantic_error::SemanticError","",4,null],[12,"identifier","","",4,null],[13,"UnaryOperatorTypeError","mc_symbol_table::semantic_error","",4,null],[12,"span","mc_symbol_table::semantic_error::SemanticError","",4,null],[12,"op","","",4,null],[12,"ty","","",4,null],[13,"UnaryOperatorCombinationError","mc_symbol_table::semantic_error","",4,null],[12,"span","mc_symbol_table::semantic_error::SemanticError","",4,null],[12,"outer","","",4,null],[12,"inner","","",4,null],[13,"MissingReturnStatement","mc_symbol_table::semantic_error","Error when a non-void function is missing a return…",4,null],[12,"span","mc_symbol_table::semantic_error::SemanticError","",4,null],[12,"identifier","","",4,null],[13,"InvalidAmountOfArguments","mc_symbol_table::semantic_error","",4,null],[12,"span","mc_symbol_table::semantic_error::SemanticError","",4,null],[12,"identifier","","",4,null],[12,"expected","","",4,null],[12,"actual","","",4,null],[13,"InvalidArgumentType","mc_symbol_table::semantic_error","",4,null],[12,"span","mc_symbol_table::semantic_error::SemanticError","",4,null],[12,"identifier","","",4,null],[12,"expected","","",4,null],[12,"actual","","",4,null],[13,"InvalidDeclarationType","mc_symbol_table::semantic_error","",4,null],[12,"span","mc_symbol_table::semantic_error::SemanticError","",4,null],[12,"identifier","","",4,null],[12,"expected","","",4,null],[12,"actual","","",4,null],[13,"InvalidReturnType","mc_symbol_table::semantic_error","",4,null],[12,"span","mc_symbol_table::semantic_error::SemanticError","",4,null],[12,"expected","","",4,null],[12,"actual","","",4,null],[13,"InvalidArgument","mc_symbol_table::semantic_error","",4,null],[12,"span","mc_symbol_table::semantic_error::SemanticError","",4,null],[12,"identifier","","",4,null],[13,"OperatorCombinationError","mc_symbol_table::semantic_error","",4,null],[12,"span","mc_symbol_table::semantic_error::SemanticError","",4,null],[12,"unary_op","","",4,null],[12,"binary_op","","",4,null],[13,"BinaryOperatorTypeCombinationError","mc_symbol_table::semantic_error","",4,null],[12,"span","mc_symbol_table::semantic_error::SemanticError","",4,null],[12,"op","","",4,null],[12,"lhs_ty","","",4,null],[12,"rhs_ty","","",4,null],[13,"BinaryOperatorTypeError","mc_symbol_table::semantic_error","",4,null],[12,"span","mc_symbol_table::semantic_error::SemanticError","",4,null],[12,"op","","",4,null],[12,"ty","","",4,null],[13,"NoMainFunction","mc_symbol_table::semantic_error","",4,null],[12,"span","mc_symbol_table::semantic_error::SemanticError","",4,null],[13,"InvalidConditionType","mc_symbol_table::semantic_error","",4,null],[12,"span","mc_symbol_table::semantic_error::SemanticError","",4,null],[12,"actual","","",4,null],[13,"InvalidCondition","mc_symbol_table::semantic_error","",4,null],[12,"span","mc_symbol_table::semantic_error::SemanticError","",4,null],[13,"InvalidUseOfVoidFunction","mc_symbol_table::semantic_error","",4,null],[12,"span","mc_symbol_table::semantic_error::SemanticError","",4,null],[12,"identifier","","",4,null],[0,"semantic_checks","mc_symbol_table","",null,null],[5,"check_main_return_type","mc_symbol_table::semantic_checks","",null,[[["functiondeclaration"]],[["result",["vec"]],["vec",["semanticerror"]]]]],[5,"check_missing_return","","",null,[[["functiondeclaration"]],[["result",["vec"]],["vec",["semanticerror"]]]]],[5,"get_expression_type","","",null,[[["expression"],["rc"]],[["option",["ty"]],["ty"]]]],[5,"check_variable","","",null,[[["span"],["identifier"],["option"],["rc"]],[["result",["vec"]],["vec",["semanticerror"]]]]],[5,"index_bounds_check","","",null,[[["span"],["identifier"],["usize"]],[["result",["vec"]],["vec",["semanticerror"]]]]],[5,"check_variable_boxed_index","","",null,[[["span"],["identifier"],["usize"],["option"],["option",["usize"]]],[["result",["vec"]],["vec",["semanticerror"]]]]],[5,"check_variable_index","","",null,[[["span"],["identifier"],["usize"],["option"],["option",["usize"]]],[["result",["vec"]],["vec",["semanticerror"]]]]],[5,"check_condition","","",null,[[["expression"],["span"],["rc"]],[["result",["vec"]],["vec",["semanticerror"]]]]],[5,"check_function_identifier_available","","",null,[[["span"],["identifier"],["rc"]],[["result",["vec"]],["vec",["semanticerror"]]]]],[5,"check_function_call","","",null,[[["span"],["identifier"],["rc"]],[["result",["vec"]],["vec",["semanticerror"]]]]],[5,"check_function_call_arguments","","",null,[[["span"],["identifier"],["rc"]],[["result",["vec"]],["vec",["semanticerror"]]]]],[5,"check_function_call_argument_type","","",null,[[["span"],["identifier"],["expression"],["rc"]],[["result",["vec"]],["vec",["semanticerror"]]]]],[5,"check_unary_expression","","",null,[[["unaryop"],["span"],["expression"],["rc"]],[["result",["vec"]],["vec",["semanticerror"]]]]],[5,"check_binary_expression","","",null,[[["span"],["expression"],["rc"],["binaryop"]],[["result",["vec"]],["vec",["semanticerror"]]]]],[5,"check_unary_operator_compatability","","",null,[[["unaryop"],["span"],["ty"]],[["result",["vec"]],["vec",["semanticerror"]]]]],[5,"check_binary_operator_compatibility","","",null,[[["span"],["ty"],["binaryop"]],[["result",["vec"]],["vec",["semanticerror"]]]]],[5,"check_unary_operator_combination","","",null,[[["unaryop"],["span"]],[["result",["vec"]],["vec",["semanticerror"]]]]],[5,"check_operator_combination","","",null,[[["unaryop"],["span"],["binaryop"]],[["result",["vec"]],["vec",["semanticerror"]]]]],[8,"CheckSemantics","","",null,null],[10,"check_semantics","","",5,[[["self"],["rc"]],[["result",["vec"]],["vec",["semanticerror"]]]]],[8,"FindReturnStatement","","",null,null],[10,"find_return_statement","","",6,[[["self"]],["bool"]]],[14,"push_error","mc_symbol_table","",null,null],[14,"extend_errors","","",null,null],[11,"from","mc_symbol_table::symbol_table","",0,[[["t"]],["t"]]],[11,"into","","",0,[[],["u"]]],[11,"to_string","","",0,[[["self"]],["string"]]],[11,"try_from","","",0,[[["u"]],["result"]]],[11,"try_into","","",0,[[],["result"]]],[11,"borrow","","",0,[[["self"]],["t"]]],[11,"borrow_mut","","",0,[[["self"]],["t"]]],[11,"type_id","","",0,[[["self"]],["typeid"]]],[11,"from","","",1,[[["t"]],["t"]]],[11,"into","","",1,[[],["u"]]],[11,"try_from","","",1,[[["u"]],["result"]]],[11,"try_into","","",1,[[],["result"]]],[11,"borrow","","",1,[[["self"]],["t"]]],[11,"borrow_mut","","",1,[[["self"]],["t"]]],[11,"type_id","","",1,[[["self"]],["typeid"]]],[11,"from","","",2,[[["t"]],["t"]]],[11,"into","","",2,[[],["u"]]],[11,"to_owned","","",2,[[["self"]],["t"]]],[11,"clone_into","","",2,[[["self"],["t"]]]],[11,"to_string","","",2,[[["self"]],["string"]]],[11,"try_from","","",2,[[["u"]],["result"]]],[11,"try_into","","",2,[[],["result"]]],[11,"borrow","","",2,[[["self"]],["t"]]],[11,"borrow_mut","","",2,[[["self"]],["t"]]],[11,"type_id","","",2,[[["self"]],["typeid"]]],[11,"from","mc_symbol_table::semantic_error","",4,[[["t"]],["t"]]],[11,"into","","",4,[[],["u"]]],[11,"to_string","","",4,[[["self"]],["string"]]],[11,"try_from","","",4,[[["u"]],["result"]]],[11,"try_into","","",4,[[],["result"]]],[11,"borrow","","",4,[[["self"]],["t"]]],[11,"borrow_mut","","",4,[[["self"]],["t"]]],[11,"type_id","","",4,[[["self"]],["typeid"]]],[11,"clone","mc_symbol_table::symbol_table","",2,[[["self"]],["symbol"]]],[11,"default","","",0,[[],["scope"]]],[11,"default","","",1,[[],["symboltable"]]],[11,"eq","","",2,[[["symbol"],["self"]],["bool"]]],[11,"ne","","",2,[[["symbol"],["self"]],["bool"]]],[11,"eq","mc_symbol_table::semantic_error","",4,[[["self"],["semanticerror"]],["bool"]]],[11,"ne","","",4,[[["self"],["semanticerror"]],["bool"]]],[11,"deref","mc_symbol_table::symbol_table","",1,[[["self"]]]],[11,"deref_mut","","",1,[[["self"]]]],[11,"fmt","","",0,[[["formatter"],["self"]],["result"]]],[11,"fmt","","",2,[[["formatter"],["self"]],["result"]]],[11,"fmt","","",1,[[["formatter"],["self"]],["result"]]],[11,"fmt","mc_symbol_table::semantic_error","",4,[[["formatter"],["self"]],["result"]]],[11,"fmt","mc_symbol_table::symbol_table","",0,[[["formatter"],["self"]],["result"]]],[11,"fmt","","",2,[[["formatter"],["self"]],["result"]]],[11,"fmt","mc_symbol_table::semantic_error","",4,[[["formatter"],["self"]],["result"]]],[11,"to_pretty_table","mc_symbol_table::symbol_table","",0,[[["self"],["table"]]]]],"p":[[3,"Scope"],[3,"SymbolTable"],[4,"Symbol"],[8,"AddToScope"],[4,"SemanticError"],[8,"CheckSemantics"],[8,"FindReturnStatement"]]};
addSearchOptions(searchIndex);initSearch(searchIndex);
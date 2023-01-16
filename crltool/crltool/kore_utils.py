from typing import (
    Optional,
    Set,
)

from pyk.kore.syntax import (
    Attr,
    Definition,
    Import,
    Module,
    Sort,
    Symbol,
    SymbolDecl,
)

class DefinitionError(Exception):
    pass

def get_module_by_name(definition: Definition, module_name: str) -> Module:
    for m in definition.modules:
        if m.name == module_name:
            return m

    #return None
    raise DefinitionError("Module '" + module_name + "' not found")

def get_all_imported_module_names(definition: Definition, module_name: str) -> Set[str]:
    module = get_module_by_name(definition, module_name)
    names : Set[str] = set()
    for s in module.sentences:
        match s:
            case Import(imported_module_name, _):
                names.add(imported_module_name)
    return names

def get_symbol_decl_from_module(module: Module, symbol_name: str) -> Optional[SymbolDecl]:
    for s in module.sentences:
        match s:
            case SymbolDecl(symbol, _, _, _, _):
                if symbol.name == symbol_name:
                    return s
    return None

def get_symbol_decl_from_definition(definition: Definition, main_module_name: str, symbol_name: str) -> SymbolDecl:
    module_names = {main_module_name}.union(get_all_imported_module_names(definition, main_module_name))
    modules = map(lambda name: get_module_by_name(definition, name), module_names)
    decls = [decl for decl in map(lambda module: get_symbol_decl_from_module(module, symbol_name), modules) if decl is not None]
    if len(list(decls)) >= 1:
        return decls[0]
    raise DefinitionError("No symbol '" + symbol_name + "' found in '" + main_module_name + "' (or recursively imported modules)")

def get_symbol_sort(definition: Definition, main_module_name: str, symbol_name: str) -> Sort:
    decl = get_symbol_decl_from_definition(definition, main_module_name, symbol_name)
    return decl.sort


def get_top_cell_initializer(definition: Definition) -> str:
    for a in definition.attrs:
        if a.symbol == "topCellInitializer":
            match a.params[0]:
                case Attr(sym, _, _):
                    return sym
    raise DefinitionError("topCellInitializer not found")
    

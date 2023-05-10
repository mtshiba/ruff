// File automatically generated by ast/asdl_rs.py.

#[derive(Clone, Debug, PartialEq)]
pub struct ModModule<U = ()> {
    pub body: Vec<Stmt<U>>,
    pub type_ignores: Vec<TypeIgnore>,
}

impl<U> From<ModModule<U>> for Mod<U> {
    fn from(payload: ModModule<U>) -> Self {
        Mod::Module(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ModInteractive<U = ()> {
    pub body: Vec<Stmt<U>>,
}

impl<U> From<ModInteractive<U>> for Mod<U> {
    fn from(payload: ModInteractive<U>) -> Self {
        Mod::Interactive(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ModExpression<U = ()> {
    pub body: Box<Expr<U>>,
}

impl<U> From<ModExpression<U>> for Mod<U> {
    fn from(payload: ModExpression<U>) -> Self {
        Mod::Expression(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ModFunctionType<U = ()> {
    pub argtypes: Vec<Expr<U>>,
    pub returns: Box<Expr<U>>,
}

impl<U> From<ModFunctionType<U>> for Mod<U> {
    fn from(payload: ModFunctionType<U>) -> Self {
        Mod::FunctionType(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Mod<U = ()> {
    Module(ModModule<U>),
    Interactive(ModInteractive<U>),
    Expression(ModExpression<U>),
    FunctionType(ModFunctionType<U>),
}

#[derive(Clone, Debug, PartialEq)]
pub struct StmtFunctionDef<U = ()> {
    pub name: Identifier,
    pub args: Box<Arguments<U>>,
    pub body: Vec<Stmt<U>>,
    pub decorator_list: Vec<Expr<U>>,
    pub returns: Option<Box<Expr<U>>>,
    pub type_comment: Option<String>,
}

impl<U> From<StmtFunctionDef<U>> for StmtKind<U> {
    fn from(payload: StmtFunctionDef<U>) -> Self {
        StmtKind::FunctionDef(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct StmtAsyncFunctionDef<U = ()> {
    pub name: Identifier,
    pub args: Box<Arguments<U>>,
    pub body: Vec<Stmt<U>>,
    pub decorator_list: Vec<Expr<U>>,
    pub returns: Option<Box<Expr<U>>>,
    pub type_comment: Option<String>,
}

impl<U> From<StmtAsyncFunctionDef<U>> for StmtKind<U> {
    fn from(payload: StmtAsyncFunctionDef<U>) -> Self {
        StmtKind::AsyncFunctionDef(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct StmtClassDef<U = ()> {
    pub name: Identifier,
    pub bases: Vec<Expr<U>>,
    pub keywords: Vec<Keyword<U>>,
    pub body: Vec<Stmt<U>>,
    pub decorator_list: Vec<Expr<U>>,
}

impl<U> From<StmtClassDef<U>> for StmtKind<U> {
    fn from(payload: StmtClassDef<U>) -> Self {
        StmtKind::ClassDef(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct StmtReturn<U = ()> {
    pub value: Option<Box<Expr<U>>>,
}

impl<U> From<StmtReturn<U>> for StmtKind<U> {
    fn from(payload: StmtReturn<U>) -> Self {
        StmtKind::Return(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct StmtDelete<U = ()> {
    pub targets: Vec<Expr<U>>,
}

impl<U> From<StmtDelete<U>> for StmtKind<U> {
    fn from(payload: StmtDelete<U>) -> Self {
        StmtKind::Delete(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct StmtAssign<U = ()> {
    pub targets: Vec<Expr<U>>,
    pub value: Box<Expr<U>>,
    pub type_comment: Option<String>,
}

impl<U> From<StmtAssign<U>> for StmtKind<U> {
    fn from(payload: StmtAssign<U>) -> Self {
        StmtKind::Assign(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct StmtAugAssign<U = ()> {
    pub target: Box<Expr<U>>,
    pub op: Operator,
    pub value: Box<Expr<U>>,
}

impl<U> From<StmtAugAssign<U>> for StmtKind<U> {
    fn from(payload: StmtAugAssign<U>) -> Self {
        StmtKind::AugAssign(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct StmtAnnAssign<U = ()> {
    pub target: Box<Expr<U>>,
    pub annotation: Box<Expr<U>>,
    pub value: Option<Box<Expr<U>>>,
    pub simple: Int,
}

impl<U> From<StmtAnnAssign<U>> for StmtKind<U> {
    fn from(payload: StmtAnnAssign<U>) -> Self {
        StmtKind::AnnAssign(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct StmtFor<U = ()> {
    pub target: Box<Expr<U>>,
    pub iter: Box<Expr<U>>,
    pub body: Vec<Stmt<U>>,
    pub orelse: Vec<Stmt<U>>,
    pub type_comment: Option<String>,
}

impl<U> From<StmtFor<U>> for StmtKind<U> {
    fn from(payload: StmtFor<U>) -> Self {
        StmtKind::For(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct StmtAsyncFor<U = ()> {
    pub target: Box<Expr<U>>,
    pub iter: Box<Expr<U>>,
    pub body: Vec<Stmt<U>>,
    pub orelse: Vec<Stmt<U>>,
    pub type_comment: Option<String>,
}

impl<U> From<StmtAsyncFor<U>> for StmtKind<U> {
    fn from(payload: StmtAsyncFor<U>) -> Self {
        StmtKind::AsyncFor(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct StmtWhile<U = ()> {
    pub test: Box<Expr<U>>,
    pub body: Vec<Stmt<U>>,
    pub orelse: Vec<Stmt<U>>,
}

impl<U> From<StmtWhile<U>> for StmtKind<U> {
    fn from(payload: StmtWhile<U>) -> Self {
        StmtKind::While(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct StmtIf<U = ()> {
    pub test: Box<Expr<U>>,
    pub body: Vec<Stmt<U>>,
    pub orelse: Vec<Stmt<U>>,
}

impl<U> From<StmtIf<U>> for StmtKind<U> {
    fn from(payload: StmtIf<U>) -> Self {
        StmtKind::If(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct StmtWith<U = ()> {
    pub items: Vec<Withitem<U>>,
    pub body: Vec<Stmt<U>>,
    pub type_comment: Option<String>,
}

impl<U> From<StmtWith<U>> for StmtKind<U> {
    fn from(payload: StmtWith<U>) -> Self {
        StmtKind::With(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct StmtAsyncWith<U = ()> {
    pub items: Vec<Withitem<U>>,
    pub body: Vec<Stmt<U>>,
    pub type_comment: Option<String>,
}

impl<U> From<StmtAsyncWith<U>> for StmtKind<U> {
    fn from(payload: StmtAsyncWith<U>) -> Self {
        StmtKind::AsyncWith(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct StmtMatch<U = ()> {
    pub subject: Box<Expr<U>>,
    pub cases: Vec<MatchCase<U>>,
}

impl<U> From<StmtMatch<U>> for StmtKind<U> {
    fn from(payload: StmtMatch<U>) -> Self {
        StmtKind::Match(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct StmtRaise<U = ()> {
    pub exc: Option<Box<Expr<U>>>,
    pub cause: Option<Box<Expr<U>>>,
}

impl<U> From<StmtRaise<U>> for StmtKind<U> {
    fn from(payload: StmtRaise<U>) -> Self {
        StmtKind::Raise(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct StmtTry<U = ()> {
    pub body: Vec<Stmt<U>>,
    pub handlers: Vec<Excepthandler<U>>,
    pub orelse: Vec<Stmt<U>>,
    pub finalbody: Vec<Stmt<U>>,
}

impl<U> From<StmtTry<U>> for StmtKind<U> {
    fn from(payload: StmtTry<U>) -> Self {
        StmtKind::Try(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct StmtTryStar<U = ()> {
    pub body: Vec<Stmt<U>>,
    pub handlers: Vec<Excepthandler<U>>,
    pub orelse: Vec<Stmt<U>>,
    pub finalbody: Vec<Stmt<U>>,
}

impl<U> From<StmtTryStar<U>> for StmtKind<U> {
    fn from(payload: StmtTryStar<U>) -> Self {
        StmtKind::TryStar(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct StmtAssert<U = ()> {
    pub test: Box<Expr<U>>,
    pub msg: Option<Box<Expr<U>>>,
}

impl<U> From<StmtAssert<U>> for StmtKind<U> {
    fn from(payload: StmtAssert<U>) -> Self {
        StmtKind::Assert(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct StmtImport<U = ()> {
    pub names: Vec<Alias<U>>,
}

impl<U> From<StmtImport<U>> for StmtKind<U> {
    fn from(payload: StmtImport<U>) -> Self {
        StmtKind::Import(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct StmtImportFrom<U = ()> {
    pub module: Option<Identifier>,
    pub names: Vec<Alias<U>>,
    pub level: Option<Int>,
}

impl<U> From<StmtImportFrom<U>> for StmtKind<U> {
    fn from(payload: StmtImportFrom<U>) -> Self {
        StmtKind::ImportFrom(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct StmtGlobal {
    pub names: Vec<Identifier>,
}

impl From<StmtGlobal> for StmtKind {
    fn from(payload: StmtGlobal) -> Self {
        StmtKind::Global(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct StmtNonlocal {
    pub names: Vec<Identifier>,
}

impl From<StmtNonlocal> for StmtKind {
    fn from(payload: StmtNonlocal) -> Self {
        StmtKind::Nonlocal(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct StmtExpr<U = ()> {
    pub value: Box<Expr<U>>,
}

impl<U> From<StmtExpr<U>> for StmtKind<U> {
    fn from(payload: StmtExpr<U>) -> Self {
        StmtKind::Expr(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum StmtKind<U = ()> {
    FunctionDef(StmtFunctionDef<U>),
    AsyncFunctionDef(StmtAsyncFunctionDef<U>),
    ClassDef(StmtClassDef<U>),
    Return(StmtReturn<U>),
    Delete(StmtDelete<U>),
    Assign(StmtAssign<U>),
    AugAssign(StmtAugAssign<U>),
    AnnAssign(StmtAnnAssign<U>),
    For(StmtFor<U>),
    AsyncFor(StmtAsyncFor<U>),
    While(StmtWhile<U>),
    If(StmtIf<U>),
    With(StmtWith<U>),
    AsyncWith(StmtAsyncWith<U>),
    Match(StmtMatch<U>),
    Raise(StmtRaise<U>),
    Try(StmtTry<U>),
    TryStar(StmtTryStar<U>),
    Assert(StmtAssert<U>),
    Import(StmtImport<U>),
    ImportFrom(StmtImportFrom<U>),
    Global(StmtGlobal),
    Nonlocal(StmtNonlocal),
    Expr(StmtExpr<U>),
    Pass,
    Break,
    Continue,
}
pub type Stmt<U = ()> = Attributed<StmtKind<U>, U>;

#[derive(Clone, Debug, PartialEq)]
pub struct ExprBoolOp<U = ()> {
    pub op: Boolop,
    pub values: Vec<Expr<U>>,
}

impl<U> From<ExprBoolOp<U>> for ExprKind<U> {
    fn from(payload: ExprBoolOp<U>) -> Self {
        ExprKind::BoolOp(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ExprNamedExpr<U = ()> {
    pub target: Box<Expr<U>>,
    pub value: Box<Expr<U>>,
}

impl<U> From<ExprNamedExpr<U>> for ExprKind<U> {
    fn from(payload: ExprNamedExpr<U>) -> Self {
        ExprKind::NamedExpr(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ExprBinOp<U = ()> {
    pub left: Box<Expr<U>>,
    pub op: Operator,
    pub right: Box<Expr<U>>,
}

impl<U> From<ExprBinOp<U>> for ExprKind<U> {
    fn from(payload: ExprBinOp<U>) -> Self {
        ExprKind::BinOp(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ExprUnaryOp<U = ()> {
    pub op: Unaryop,
    pub operand: Box<Expr<U>>,
}

impl<U> From<ExprUnaryOp<U>> for ExprKind<U> {
    fn from(payload: ExprUnaryOp<U>) -> Self {
        ExprKind::UnaryOp(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ExprLambda<U = ()> {
    pub args: Box<Arguments<U>>,
    pub body: Box<Expr<U>>,
}

impl<U> From<ExprLambda<U>> for ExprKind<U> {
    fn from(payload: ExprLambda<U>) -> Self {
        ExprKind::Lambda(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ExprIfExp<U = ()> {
    pub test: Box<Expr<U>>,
    pub body: Box<Expr<U>>,
    pub orelse: Box<Expr<U>>,
}

impl<U> From<ExprIfExp<U>> for ExprKind<U> {
    fn from(payload: ExprIfExp<U>) -> Self {
        ExprKind::IfExp(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ExprDict<U = ()> {
    pub keys: Vec<Option<Expr<U>>>,
    pub values: Vec<Expr<U>>,
}

impl<U> From<ExprDict<U>> for ExprKind<U> {
    fn from(payload: ExprDict<U>) -> Self {
        ExprKind::Dict(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ExprSet<U = ()> {
    pub elts: Vec<Expr<U>>,
}

impl<U> From<ExprSet<U>> for ExprKind<U> {
    fn from(payload: ExprSet<U>) -> Self {
        ExprKind::Set(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ExprListComp<U = ()> {
    pub elt: Box<Expr<U>>,
    pub generators: Vec<Comprehension<U>>,
}

impl<U> From<ExprListComp<U>> for ExprKind<U> {
    fn from(payload: ExprListComp<U>) -> Self {
        ExprKind::ListComp(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ExprSetComp<U = ()> {
    pub elt: Box<Expr<U>>,
    pub generators: Vec<Comprehension<U>>,
}

impl<U> From<ExprSetComp<U>> for ExprKind<U> {
    fn from(payload: ExprSetComp<U>) -> Self {
        ExprKind::SetComp(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ExprDictComp<U = ()> {
    pub key: Box<Expr<U>>,
    pub value: Box<Expr<U>>,
    pub generators: Vec<Comprehension<U>>,
}

impl<U> From<ExprDictComp<U>> for ExprKind<U> {
    fn from(payload: ExprDictComp<U>) -> Self {
        ExprKind::DictComp(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ExprGeneratorExp<U = ()> {
    pub elt: Box<Expr<U>>,
    pub generators: Vec<Comprehension<U>>,
}

impl<U> From<ExprGeneratorExp<U>> for ExprKind<U> {
    fn from(payload: ExprGeneratorExp<U>) -> Self {
        ExprKind::GeneratorExp(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ExprAwait<U = ()> {
    pub value: Box<Expr<U>>,
}

impl<U> From<ExprAwait<U>> for ExprKind<U> {
    fn from(payload: ExprAwait<U>) -> Self {
        ExprKind::Await(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ExprYield<U = ()> {
    pub value: Option<Box<Expr<U>>>,
}

impl<U> From<ExprYield<U>> for ExprKind<U> {
    fn from(payload: ExprYield<U>) -> Self {
        ExprKind::Yield(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ExprYieldFrom<U = ()> {
    pub value: Box<Expr<U>>,
}

impl<U> From<ExprYieldFrom<U>> for ExprKind<U> {
    fn from(payload: ExprYieldFrom<U>) -> Self {
        ExprKind::YieldFrom(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ExprCompare<U = ()> {
    pub left: Box<Expr<U>>,
    pub ops: Vec<Cmpop>,
    pub comparators: Vec<Expr<U>>,
}

impl<U> From<ExprCompare<U>> for ExprKind<U> {
    fn from(payload: ExprCompare<U>) -> Self {
        ExprKind::Compare(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ExprCall<U = ()> {
    pub func: Box<Expr<U>>,
    pub args: Vec<Expr<U>>,
    pub keywords: Vec<Keyword<U>>,
}

impl<U> From<ExprCall<U>> for ExprKind<U> {
    fn from(payload: ExprCall<U>) -> Self {
        ExprKind::Call(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ExprFormattedValue<U = ()> {
    pub value: Box<Expr<U>>,
    pub conversion: Int,
    pub format_spec: Option<Box<Expr<U>>>,
}

impl<U> From<ExprFormattedValue<U>> for ExprKind<U> {
    fn from(payload: ExprFormattedValue<U>) -> Self {
        ExprKind::FormattedValue(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ExprJoinedStr<U = ()> {
    pub values: Vec<Expr<U>>,
}

impl<U> From<ExprJoinedStr<U>> for ExprKind<U> {
    fn from(payload: ExprJoinedStr<U>) -> Self {
        ExprKind::JoinedStr(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ExprConstant {
    pub value: Constant,
    pub kind: Option<String>,
}

impl From<ExprConstant> for ExprKind {
    fn from(payload: ExprConstant) -> Self {
        ExprKind::Constant(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ExprAttribute<U = ()> {
    pub value: Box<Expr<U>>,
    pub attr: Identifier,
    pub ctx: ExprContext,
}

impl<U> From<ExprAttribute<U>> for ExprKind<U> {
    fn from(payload: ExprAttribute<U>) -> Self {
        ExprKind::Attribute(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ExprSubscript<U = ()> {
    pub value: Box<Expr<U>>,
    pub slice: Box<Expr<U>>,
    pub ctx: ExprContext,
}

impl<U> From<ExprSubscript<U>> for ExprKind<U> {
    fn from(payload: ExprSubscript<U>) -> Self {
        ExprKind::Subscript(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ExprStarred<U = ()> {
    pub value: Box<Expr<U>>,
    pub ctx: ExprContext,
}

impl<U> From<ExprStarred<U>> for ExprKind<U> {
    fn from(payload: ExprStarred<U>) -> Self {
        ExprKind::Starred(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ExprName {
    pub id: Identifier,
    pub ctx: ExprContext,
}

impl From<ExprName> for ExprKind {
    fn from(payload: ExprName) -> Self {
        ExprKind::Name(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ExprList<U = ()> {
    pub elts: Vec<Expr<U>>,
    pub ctx: ExprContext,
}

impl<U> From<ExprList<U>> for ExprKind<U> {
    fn from(payload: ExprList<U>) -> Self {
        ExprKind::List(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ExprTuple<U = ()> {
    pub elts: Vec<Expr<U>>,
    pub ctx: ExprContext,
}

impl<U> From<ExprTuple<U>> for ExprKind<U> {
    fn from(payload: ExprTuple<U>) -> Self {
        ExprKind::Tuple(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ExprSlice<U = ()> {
    pub lower: Option<Box<Expr<U>>>,
    pub upper: Option<Box<Expr<U>>>,
    pub step: Option<Box<Expr<U>>>,
}

impl<U> From<ExprSlice<U>> for ExprKind<U> {
    fn from(payload: ExprSlice<U>) -> Self {
        ExprKind::Slice(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum ExprKind<U = ()> {
    BoolOp(ExprBoolOp<U>),
    NamedExpr(ExprNamedExpr<U>),
    BinOp(ExprBinOp<U>),
    UnaryOp(ExprUnaryOp<U>),
    Lambda(ExprLambda<U>),
    IfExp(ExprIfExp<U>),
    Dict(ExprDict<U>),
    Set(ExprSet<U>),
    ListComp(ExprListComp<U>),
    SetComp(ExprSetComp<U>),
    DictComp(ExprDictComp<U>),
    GeneratorExp(ExprGeneratorExp<U>),
    Await(ExprAwait<U>),
    Yield(ExprYield<U>),
    YieldFrom(ExprYieldFrom<U>),
    Compare(ExprCompare<U>),
    Call(ExprCall<U>),
    FormattedValue(ExprFormattedValue<U>),
    JoinedStr(ExprJoinedStr<U>),
    Constant(ExprConstant),
    Attribute(ExprAttribute<U>),
    Subscript(ExprSubscript<U>),
    Starred(ExprStarred<U>),
    Name(ExprName),
    List(ExprList<U>),
    Tuple(ExprTuple<U>),
    Slice(ExprSlice<U>),
}
pub type Expr<U = ()> = Attributed<ExprKind<U>, U>;

#[derive(Clone, Debug, PartialEq)]
pub enum ExprContext {
    Load,
    Store,
    Del,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Boolop {
    And,
    Or,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Operator {
    Add,
    Sub,
    Mult,
    MatMult,
    Div,
    Mod,
    Pow,
    LShift,
    RShift,
    BitOr,
    BitXor,
    BitAnd,
    FloorDiv,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Unaryop {
    Invert,
    Not,
    UAdd,
    USub,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Cmpop {
    Eq,
    NotEq,
    Lt,
    LtE,
    Gt,
    GtE,
    Is,
    IsNot,
    In,
    NotIn,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Comprehension<U = ()> {
    pub target: Expr<U>,
    pub iter: Expr<U>,
    pub ifs: Vec<Expr<U>>,
    pub is_async: Int,
}

#[derive(Clone, Debug, PartialEq)]
pub struct ExcepthandlerExceptHandler<U = ()> {
    pub type_: Option<Box<Expr<U>>>,
    pub name: Option<Identifier>,
    pub body: Vec<Stmt<U>>,
}

impl<U> From<ExcepthandlerExceptHandler<U>> for ExcepthandlerKind<U> {
    fn from(payload: ExcepthandlerExceptHandler<U>) -> Self {
        ExcepthandlerKind::ExceptHandler(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum ExcepthandlerKind<U = ()> {
    ExceptHandler(ExcepthandlerExceptHandler<U>),
}
pub type Excepthandler<U = ()> = Attributed<ExcepthandlerKind<U>, U>;

#[derive(Clone, Debug, PartialEq)]
pub struct Arguments<U = ()> {
    pub posonlyargs: Vec<Arg<U>>,
    pub args: Vec<Arg<U>>,
    pub vararg: Option<Box<Arg<U>>>,
    pub kwonlyargs: Vec<Arg<U>>,
    pub kw_defaults: Vec<Expr<U>>,
    pub kwarg: Option<Box<Arg<U>>>,
    pub defaults: Vec<Expr<U>>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct ArgData<U = ()> {
    pub arg: Identifier,
    pub annotation: Option<Box<Expr<U>>>,
    pub type_comment: Option<String>,
}
pub type Arg<U = ()> = Attributed<ArgData<U>, U>;

#[derive(Clone, Debug, PartialEq)]
pub struct KeywordData<U = ()> {
    pub arg: Option<Identifier>,
    pub value: Expr<U>,
}
pub type Keyword<U = ()> = Attributed<KeywordData<U>, U>;

#[derive(Clone, Debug, PartialEq)]
pub struct AliasData {
    pub name: Identifier,
    pub asname: Option<Identifier>,
}
pub type Alias<U = ()> = Attributed<AliasData, U>;

#[derive(Clone, Debug, PartialEq)]
pub struct Withitem<U = ()> {
    pub context_expr: Expr<U>,
    pub optional_vars: Option<Box<Expr<U>>>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct MatchCase<U = ()> {
    pub pattern: Pattern<U>,
    pub guard: Option<Box<Expr<U>>>,
    pub body: Vec<Stmt<U>>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct PatternMatchValue<U = ()> {
    pub value: Box<Expr<U>>,
}

impl<U> From<PatternMatchValue<U>> for PatternKind<U> {
    fn from(payload: PatternMatchValue<U>) -> Self {
        PatternKind::MatchValue(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct PatternMatchSingleton {
    pub value: Constant,
}

impl From<PatternMatchSingleton> for PatternKind {
    fn from(payload: PatternMatchSingleton) -> Self {
        PatternKind::MatchSingleton(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct PatternMatchSequence<U = ()> {
    pub patterns: Vec<Pattern<U>>,
}

impl<U> From<PatternMatchSequence<U>> for PatternKind<U> {
    fn from(payload: PatternMatchSequence<U>) -> Self {
        PatternKind::MatchSequence(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct PatternMatchMapping<U = ()> {
    pub keys: Vec<Expr<U>>,
    pub patterns: Vec<Pattern<U>>,
    pub rest: Option<Identifier>,
}

impl<U> From<PatternMatchMapping<U>> for PatternKind<U> {
    fn from(payload: PatternMatchMapping<U>) -> Self {
        PatternKind::MatchMapping(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct PatternMatchClass<U = ()> {
    pub cls: Box<Expr<U>>,
    pub patterns: Vec<Pattern<U>>,
    pub kwd_attrs: Vec<Identifier>,
    pub kwd_patterns: Vec<Pattern<U>>,
}

impl<U> From<PatternMatchClass<U>> for PatternKind<U> {
    fn from(payload: PatternMatchClass<U>) -> Self {
        PatternKind::MatchClass(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct PatternMatchStar {
    pub name: Option<Identifier>,
}

impl From<PatternMatchStar> for PatternKind {
    fn from(payload: PatternMatchStar) -> Self {
        PatternKind::MatchStar(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct PatternMatchAs<U = ()> {
    pub pattern: Option<Box<Pattern<U>>>,
    pub name: Option<Identifier>,
}

impl<U> From<PatternMatchAs<U>> for PatternKind<U> {
    fn from(payload: PatternMatchAs<U>) -> Self {
        PatternKind::MatchAs(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct PatternMatchOr<U = ()> {
    pub patterns: Vec<Pattern<U>>,
}

impl<U> From<PatternMatchOr<U>> for PatternKind<U> {
    fn from(payload: PatternMatchOr<U>) -> Self {
        PatternKind::MatchOr(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum PatternKind<U = ()> {
    MatchValue(PatternMatchValue<U>),
    MatchSingleton(PatternMatchSingleton),
    MatchSequence(PatternMatchSequence<U>),
    MatchMapping(PatternMatchMapping<U>),
    MatchClass(PatternMatchClass<U>),
    MatchStar(PatternMatchStar),
    MatchAs(PatternMatchAs<U>),
    MatchOr(PatternMatchOr<U>),
}
pub type Pattern<U = ()> = Attributed<PatternKind<U>, U>;

#[derive(Clone, Debug, PartialEq)]
pub struct TypeIgnoreTypeIgnore {
    pub lineno: Int,
    pub tag: String,
}

impl From<TypeIgnoreTypeIgnore> for TypeIgnore {
    fn from(payload: TypeIgnoreTypeIgnore) -> Self {
        TypeIgnore::TypeIgnore(payload)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum TypeIgnore {
    TypeIgnore(TypeIgnoreTypeIgnore),
}

%{
  /********************************************************************
   * AUTHORS: Vijay Ganesh
   *
   * BEGIN DATE: November, 2005
   *
  Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
  ********************************************************************/
  
#include "stp/Parser/parser.h"
#include "stp/cpp_interface.h"
#include "stp/Parser/LetMgr.h"
#include "stp/Parser/parser.h"

  using namespace stp;
  using std::cout;
  using std::cerr;
  using std::endl;
  
  // Suppress the bogus warning suppression in bison (it generates
  // compile error)
#undef __GNUC_MINOR__
  
#define YYLTYPE_IS_TRIVIAL 1
#define YYMAXDEPTH 1048576000
#define YYERROR_VERBOSE 1
#define YY_EXIT_FAILURE -1
  
  extern int cvclex(void);
  extern char* yytext;
  extern int cvclineno;
  int yyerror(const char *s) {
    cout << "CVC syntax error: line " << cvclineno << "\n" << s << endl;
    FatalError("");
    return YY_EXIT_FAILURE;
  }
  int yyerror(void* /*AssertsQuery*/, const char* s) { return yyerror(s); }
  
  %}

%parse-param {void* AssertsQuery}

%union {

  unsigned int uintval;                 /* for numerals in types. */
  struct {
    //stores the indexwidth and valuewidth
    //indexwidth is 0 iff type is bitvector. positive iff type is
    //array, and stores the width of the indexing bitvector
    unsigned int indexwidth;
    //width of the bitvector type
    unsigned int valuewidth;
  } indexvaluewidth;

  //ASTNode,ASTVec
  stp::ASTNode *node;
  stp::ASTVec *vec;
  vector<char*> * stringVec;
  char* str;

  //Hash_Map to hold Array Updates during parse A map from array index
  //to array values. To support the WITH construct
  stp::ASTNodeMap * Index_To_UpdateValue;
};

%start cmd

%token  AND_TOK                 "AND"
%token  OR_TOK                  "OR"
%token  NOT_TOK                 "NOT"
%token  EXCEPT_TOK              "EXCEPT"
%token  XOR_TOK                 "XOR"
%token  NAND_TOK                "NAND"
%token  NOR_TOK                 "NOR"
%token  IMPLIES_TOK             "=>"
%token  IFF_TOK                 "<=>"

%token  IF_TOK                  "IF"
%token  THEN_TOK                "THEN"
%token  ELSE_TOK                "ELSE"
%token  ELSIF_TOK               "ELSIF"
%token  END_TOK                 "END"
%token  ENDIF_TOK               "ENDIF"
%token  NEQ_TOK                 "/="
%token  ASSIGN_TOK              ":="

%token  BV_TOK                  "BV"
%token  BVLEFTSHIFT_TOK         "<<"
%token  BVRIGHTSHIFT_TOK        ">>"

%token  BVSHL_TOK               "BVSHL"
%token  BVLSHR_TOK              "BVLSHR"
%token  BVASHR_TOK              "BVASHR"

%token  BVPLUS_TOK              "BVPLUS"
%token  BVSUB_TOK               "BVSUB"
%token  BVUMINUS_TOK            "BVUMINUS"
%token  BVMULT_TOK              "BVMULT"

%token  BVDIV_TOK               "BVDIV"
%token  BVMOD_TOK               "BVMOD"
%token  SBVDIV_TOK              "SBVDIV"
%token  SBVREM_TOK              "SBVREM"


%token  BVNEG_TOK               "~"
%token  BVAND_TOK               "&"
%token  BVOR_TOK                "|"
%token  BVXOR_TOK               "BVXOR"
%token  BVNAND_TOK              "BVNAND"
%token  BVNOR_TOK               "BVNOR"
%token  BVXNOR_TOK              "BVXNOR"
%token  BVCONCAT_TOK            "@"

%token  BVLT_TOK                "BVLT"
%token  BVGT_TOK                "BVGT"
%token  BVLE_TOK                "BVLE"
%token  BVGE_TOK                "BVGE"

%token  BVSLT_TOK               "BVSLT"
%token  BVSGT_TOK               "BVSGT"
%token  BVSLE_TOK               "BVSLE"
%token  BVSGE_TOK               "BVSGE"
%token  BOOL_TO_BV_TOK          "BOOLBV"
%token  BVSX_TOK                "BVSX"
%token  BVZX_TOK                "BVZX"
%token  BOOLEXTRACT_TOK         "BOOLEXTRACT"
%token  ASSERT_TOK              "ASSERT"
%token  QUERY_TOK               "QUERY"

%token  BOOLEAN_TOK             "BOOLEAN"
%token  ARRAY_TOK               "ARRAY"
%token  OF_TOK                  "OF"
%token  WITH_TOK                "WITH"

%token  TRUELIT_TOK             "TRUE"
%token  FALSELIT_TOK            "FALSE"

%token  IN_TOK                  "IN"
%token  LET_TOK                 "LET"
 //%token  COUNTEREXAMPLE_TOK      "COUNTEREXAMPLE"
%token  PUSH_TOK                "PUSH"
%token  POP_TOK                 "POP"

%left IN_TOK
%left XOR_TOK
%left IFF_TOK
%right IMPLIES_TOK
%left OR_TOK
%left AND_TOK
%left NAND_TOK
%left NOR_TOK
%left NOT_TOK
%left BVCONCAT_TOK
%left BVOR_TOK
%left BVAND_TOK
%left BVXOR_TOK
%left BVNAND_TOK
%left BVNOR_TOK
%left BVXNOR_TOK
%left BVNEG_TOK
%left BVLEFTSHIFT_TOK BVRIGHTSHIFT_TOK
%left WITH_TOK

%nonassoc '=' NEQ_TOK ASSIGN_TOK
%nonassoc BVLT_TOK BVLE_TOK BVGT_TOK BVGE_TOK
%nonassoc BVUMINUS_TOK BVPLUS_TOK BVSUB_TOK BVSX_TOK BVZX_TOK
%nonassoc '[' 
%nonassoc '{' '.' '('
%nonassoc BV_TOK

%type <vec>  Exprs 
%type <vec>  Asserts
%type <stringVec>  FORM_IDs reverseFORM_IDs  
%type <node> Expr Formula IfExpr ElseRestExpr IfForm ElseRestForm Assert Query ArrayUpdateExpr
%type <Index_To_UpdateValue> Updates

%type <indexvaluewidth>  BvType BoolType ArrayType Type 

%token <node> BVCONST_TOK
%token <node> TERMID_TOK FORMID_TOK COUNTEREXAMPLE_TOK
%token <uintval> NUMERAL_TOK
%token <str> BIN_BASED_NUMBER
%token <str> DEC_BASED_NUMBER
%token <str> HEX_BASED_NUMBER
%token <str> STRING_TOK

%%

cmd             :      other_cmd
{
  GlobalParserInterface->letMgr->_parser_symbol_table.clear();
}
|      other_cmd counterexample
{
  GlobalParserInterface->letMgr->_parser_symbol_table.clear(); 
}
; 

counterexample  :      COUNTEREXAMPLE_TOK ';'
{
  GlobalParserInterface->getUserFlags().print_counterexample_flag = true;
  (GlobalSTP->Ctr_Example)->PrintCounterExample(true);
}                              
;

other_cmd       :
/* other_cmd1 */
/* { */
/*   ASTVec aaa = GlobalParserInterface->GetAsserts(); */
/*   if(aaa.size() == 0) */
/*     { */
/*       yyerror("Fatal Error: parsing:  GetAsserts() call: no assertions: "); */
/*     } */

/*   ASTNode asserts =  */
/*     aaa.size() == 1 ?  */
/*     aaa[0] : */
/*     GlobalParserInterface->CreateNode(AND, aaa); */
/*   ((ASTVec*)AssertsQuery)->push_back(asserts);   */
/* } */
|      Query 
{ 
  ((ASTVec*)AssertsQuery)->push_back(GlobalParserInterface->CreateNode(TRUE));
  ((ASTVec*)AssertsQuery)->push_back(*$1);                       
  delete $1;
}
|      VarDecls Query 
{ 
  ((ASTVec*)AssertsQuery)->push_back(GlobalParserInterface->CreateNode(TRUE));
  ((ASTVec*)AssertsQuery)->push_back(*$2);
  delete $2;
}
|      other_cmd1 Query
{
  ASTVec aaa = GlobalParserInterface->GetAsserts();
  if(aaa.size() == 0)
    {
      yyerror("Fatal Error: parsing:  GetAsserts() call: no assertions: ");
    }

  ASTNode asserts = 
    aaa.size() == 1 ? 
    aaa[0] :
    GlobalParserInterface->CreateNode(AND, aaa);
  ((ASTVec*)AssertsQuery)->push_back(asserts);
  ((ASTVec*)AssertsQuery)->push_back(*$2);
  delete $2;
}
;

other_cmd1      :     VarDecls Asserts
{
  delete $2;
}                 
|     Asserts
{
  delete $1;
}
|     other_cmd1 VarDecls Asserts
{
  delete $3;
}
;

/* push            :     PUSH_TOK */
/*                       { */
/*                      GlobalParserBM->Push(); */
/*                       } */
/*                 | */
/*                 ; */

/* pop             :     POP_TOK */
/*                       { */
/*                      GlobalParserBM->Pop(); */
/*                       } */
/*                 | */
/*                 ; */

Asserts         :      Assert 
{
  $$ = new ASTVec;
  $$->push_back(*$1);
  GlobalParserInterface->AddAssert(*$1);
  delete $1;
}
|      Asserts Assert
{
  $1->push_back(*$2);
  GlobalParserInterface->AddAssert(*$2);
  $$ = $1;
  delete $2;
}
;

Assert          :      ASSERT_TOK Formula ';' 
{ 
  $$ = $2;
 }                
;

Query           :      QUERY_TOK Formula ';' { GlobalParserInterface->SetQuery(*$2); $$ = $2;}
; 


/* Grammar for Variable Declaration */
VarDecls        :      VarDecl ';'
{
}
|      VarDecls  VarDecl ';'
{
}
;

VarDecl         :      FORM_IDs ':' Type 
{
  for(vector<char*>::iterator i=$1->begin(),iend=$1->end();i!=iend;i++) {
    ASTNode s = stp::GlobalParserInterface->LookupOrCreateSymbol(*i);
    s.SetIndexWidth($3.indexwidth);
    s.SetValueWidth($3.valuewidth);
    GlobalParserInterface->letMgr->_parser_symbol_table.insert(s);
    GlobalParserBM->ListOfDeclaredVars.push_back(s);
  }
  delete $1;
}
|      FORM_IDs ':' Type '=' Expr
{
  //do type checking. if doesn't pass then abort
  BVTypeCheck(*$5);
  if($3.indexwidth != $5->GetIndexWidth())
    yyerror("Fatal Error: parsing: LET Expr: Type check fail: ");
  if($3.valuewidth != $5->GetValueWidth())
    yyerror("Fatal Error: parsing: LET Expr: Type check fail: ");
                         
  for(vector<char*>::iterator i=$1->begin(),iend=$1->end();i!=iend;i++) {                         
    GlobalParserInterface->letMgr->LetExprMgr(*i,*$5);
  }
    delete $5;
    delete $1;
}
|      FORM_IDs ':' Type '=' Formula
{
  //do type checking. if doesn't pass then abort
  BVTypeCheck(*$5);
  if($3.indexwidth != $5->GetIndexWidth())
    yyerror("Fatal Error: parsing: LET Expr: Type check fail: ");
  if($3.valuewidth != $5->GetValueWidth())
    yyerror("Fatal Error: parsing: LET Expr: Type check fail: ");
                         
  for(vector<char*>::iterator i=$1->begin(),iend=$1->end();i!=iend;i++) {                         
    GlobalParserInterface->letMgr->LetExprMgr(*i,*$5);
  }
  delete $5;
  delete $1;
}                
;

reverseFORM_IDs  :      STRING_TOK
{
  $$ = new vector<char*>();                      
  $$->push_back($1);
 // delete $1;
}
|      STRING_TOK ',' reverseFORM_IDs
{
  $3->push_back($1);
  $$ = $3;
 // delete $1;
}
;

FORM_IDs         :     reverseFORM_IDs
{
  $$ = new vector<char*>($1->rbegin(),$1->rend());
  delete $1;
}
;

/* Grammar for Types */
Type            :      BvType { $$ = $1; }
|      BoolType { $$ = $1; }
|      ArrayType { $$ = $1; }
;               

BvType          :      BV_TOK '(' NUMERAL_TOK ')' 
{
  /*((indexwidth is 0) && (valuewidth>0)) iff type is BV*/
  $$.indexwidth = 0;
  unsigned int length = $3;
  if(length > 0) {
    $$.valuewidth = length;
  }
  else
    FatalError("Fatal Error: parsing: BITVECTORS must be of positive length: \n");
}
;
BoolType        :      BOOLEAN_TOK
{
  $$.indexwidth = 0;
  $$.valuewidth = 0;
}
;
ArrayType       :      ARRAY_TOK BvType OF_TOK BvType
{
  $$.indexwidth = $2.valuewidth;
  $$.valuewidth = $4.valuewidth;
}
;

/*Grammar for ITEs which are a type of Term*/
IfExpr          :      IF_TOK Formula THEN_TOK Expr ElseRestExpr 
{
  unsigned int width = $4->GetValueWidth();
  if (width != $5->GetValueWidth())
    yyerror("Width mismatch in IF-THEN-ELSE");
  if($4->GetIndexWidth() != $5->GetIndexWidth())
    yyerror("Width mismatch in IF-THEN-ELSE");

  BVTypeCheck(*$2);
  BVTypeCheck(*$4);
  BVTypeCheck(*$5);
  $$ = new ASTNode(GlobalParserInterface->nf->CreateArrayTerm(ITE,$5->GetIndexWidth(), width, *$2, *$4, *$5));
  delete $2;
  delete $4;
  delete $5;
}
;

ElseRestExpr    :      ELSE_TOK Expr ENDIF_TOK  { $$ = $2; }
|      ELSIF_TOK Expr THEN_TOK Expr ElseRestExpr 
{
  unsigned int width = $2->GetValueWidth();
  if (width != $4->GetValueWidth() || width != $5->GetValueWidth())
    yyerror("Width mismatch in IF-THEN-ELSE");
  if ($2->GetIndexWidth() != $4->GetValueWidth() || $2->GetIndexWidth() != $5->GetValueWidth())
    yyerror("Width mismatch in IF-THEN-ELSE");

  BVTypeCheck(*$2);
  BVTypeCheck(*$4);
  BVTypeCheck(*$5);                     
  $$ = new ASTNode(GlobalParserInterface->nf->CreateArrayTerm(ITE, $5->GetIndexWidth(), width, *$2, *$4, *$5));
  delete $2;
  delete $4;
  delete $5;
}
;

/* Grammar for formulas */
Formula         :     '(' Formula ')' 
{
  $$ = $2; 
}
|      FORMID_TOK 
{  
  $$ = new ASTNode(GlobalParserInterface->letMgr->ResolveID(*$1)); delete $1;
}
|      FORMID_TOK '(' Expr ')' 
{
  $$ = new ASTNode(GlobalParserInterface->nf->CreateNode(PARAMBOOL,*$1,*$3));
  delete $1;
  delete $3;
}
|      BOOLEXTRACT_TOK '(' Expr ',' NUMERAL_TOK ')'
{
  unsigned int width = $3->GetValueWidth();
  if(width <= (unsigned)$5)
    yyerror("Fatal Error: BOOLEXTRACT: trying to boolextract a bit which beyond range");
                         
  ASTNode bit = GlobalParserInterface->CreateBVConst(32, $5);
  ASTNode * out = new ASTNode(GlobalParserInterface->nf->CreateNode(BOOLEXTRACT,*$3,bit));

  $$ = out;
  delete $3;
}
|      Expr '=' Expr 
{
  ASTNode * n = new ASTNode(GlobalParserInterface->nf->CreateNode(EQ, *$1, *$3));
  $$ = n;
  delete $1;
  delete $3;
} 
|      Expr NEQ_TOK Expr 
{
  ASTNode * n = new ASTNode(GlobalParserInterface->nf->CreateNode(NOT, GlobalParserInterface->nf->CreateNode(EQ, *$1, *$3)));
  $$ = n;
  delete $1;
  delete $3;
}
|      NOT_TOK Formula 
{
  $$ = new ASTNode(GlobalParserInterface->nf->CreateNode(NOT, *$2));
  delete $2;
}
|      Formula OR_TOK Formula %prec OR_TOK 
{
  $$ = new ASTNode(GlobalParserInterface->nf->CreateNode(OR, *$1, *$3));
  delete $1;
  delete $3;
} 
|      Formula NOR_TOK Formula
{
  $$ = new ASTNode(GlobalParserInterface->nf->CreateNode(NOR, *$1, *$3));
  delete $1;
  delete $3;
} 
|      Formula AND_TOK Formula %prec AND_TOK 
{
  $$ = new ASTNode(GlobalParserInterface->nf->CreateNode(AND, *$1, *$3));
  delete $1;
  delete $3;
}
|      Formula NAND_TOK Formula
{
  $$ = new ASTNode(GlobalParserInterface->nf->CreateNode(NAND, *$1, *$3));
  delete $1;
  delete $3;
}
|      Formula IMPLIES_TOK Formula
{
  $$ = new ASTNode(GlobalParserInterface->nf->CreateNode(IMPLIES, *$1, *$3));
  delete $1;
  delete $3;
}
|      Formula IFF_TOK Formula
{
  $$ = new ASTNode(GlobalParserInterface->nf->CreateNode(IFF, *$1, *$3));
  delete $1;
  delete $3;
} 
|      Formula XOR_TOK Formula
{
  $$ = new ASTNode(GlobalParserInterface->nf->CreateNode(XOR, *$1, *$3));
  delete $1;
  delete $3;
} 
|      BVLT_TOK '(' Expr ',' Expr ')' 
{
  ASTNode * n = new ASTNode(GlobalParserInterface->nf->CreateNode(BVLT, *$3, *$5));
  $$ = n;
  delete $3;
  delete $5;
}
|      BVGT_TOK '(' Expr ',' Expr ')' 
{
  ASTNode * n = new ASTNode(GlobalParserInterface->nf->CreateNode(BVGT, *$3, *$5));
  $$ = n;
  delete $3;
  delete $5;
}
|      BVLE_TOK '(' Expr ',' Expr ')' 
{
  ASTNode * n = new ASTNode(GlobalParserInterface->nf->CreateNode(BVLE, *$3, *$5));
  $$ = n;
  delete $3;
  delete $5;
}
|      BVGE_TOK '(' Expr ',' Expr ')' 
{
  ASTNode * n = new ASTNode(GlobalParserInterface->nf->CreateNode(BVGE, *$3, *$5));
  $$ = n;
  delete $3;
  delete $5;
}
|      BVSLT_TOK '(' Expr ',' Expr ')' 
{
  ASTNode * n = new ASTNode(GlobalParserInterface->nf->CreateNode(BVSLT, *$3, *$5));
  $$ = n;
  delete $3;
  delete $5;
}
|      BVSGT_TOK '(' Expr ',' Expr ')' 
{
  ASTNode * n = new ASTNode(GlobalParserInterface->nf->CreateNode(BVSGT, *$3, *$5));
  $$ = n;
  delete $3;
  delete $5;
}
|      BVSLE_TOK '(' Expr ',' Expr ')' 
{
  ASTNode * n = new ASTNode(GlobalParserInterface->nf->CreateNode(BVSLE, *$3, *$5));
  $$ = n;
  delete $3;
  delete $5;
}
|      BVSGE_TOK '(' Expr ',' Expr ')' 
{
  ASTNode * n = new ASTNode(GlobalParserInterface->nf->CreateNode(BVSGE, *$3, *$5));
  $$ = n;
  delete $3;
  delete $5;
}
|      IfForm
|      TRUELIT_TOK 
{
  $$ = new ASTNode(GlobalParserInterface->CreateNode(TRUE)); 
  assert($$->GetIndexWidth() == 0);
  assert($$->GetValueWidth() == 0);
}
|      FALSELIT_TOK 
{ 
  $$ = new ASTNode(GlobalParserInterface->CreateNode(FALSE)); 
  assert($$->GetIndexWidth() == 0);
  assert($$->GetValueWidth() == 0);
}

|      LET_TOK LetDecls IN_TOK Formula
{
  $$ = $4;
  //Cleanup the LetIDToExprMap
  GlobalParserInterface->letMgr->CleanupLetIDMap();
}
;

/*Grammar for ITEs which are Formulas */
IfForm          :      IF_TOK Formula THEN_TOK Formula ElseRestForm 
{
  $$ = new ASTNode(GlobalParserInterface->nf->CreateNode(ITE, *$2, *$4, *$5));
  delete $2;
  delete $4;
  delete $5;
}
;

ElseRestForm    :      ELSE_TOK Formula ENDIF_TOK  { $$ = $2; }
|      ELSIF_TOK Formula THEN_TOK Formula ElseRestForm 
{
  $$ = new ASTNode(GlobalParserInterface->nf->CreateNode(ITE, *$2, *$4, *$5));
  delete $2;
  delete $4;
  delete $5;
} | STRING_TOK
{
   cerr << "Unresolved symbol:" << $1 << endl;
   yyerror("bad symbol");
}
;

/*Grammar for a list of expressions*/
Exprs           :      Expr 
{
  $$ = new ASTVec;
  BVTypeCheck(*$1);
  $$->push_back(*$1);
  delete $1;
}
|      Exprs ',' Expr 
{
  $1->push_back(*$3);
  BVTypeCheck(*$3);
  $$ = $1; 
  delete $3;
}
;

/* Grammar for Expr */
Expr            :      TERMID_TOK { $$ = new ASTNode(GlobalParserInterface->letMgr->ResolveID(*$1)); delete $1;}
|      '(' Expr ')' { $$ = $2; }
|      BVCONST_TOK { $$ = $1; }
|      BOOL_TO_BV_TOK '(' Formula ')'           
{
  BVTypeCheck(*$3);
  ASTNode one = GlobalParserInterface->CreateBVConst(1,1);
  ASTNode zero = GlobalParserInterface->CreateBVConst(1,0);

  //return ITE(*$3, length(1), 0bin1, 0bin0)
  $$ = new ASTNode(GlobalParserInterface->nf->CreateTerm(ITE,1,*$3,one,zero));
  delete $3;
}
| NUMERAL_TOK BIN_BASED_NUMBER 
{ 
  std::string vals($2);
  $$ = new ASTNode(GlobalParserInterface->CreateBVConst(vals, 2, $1));
  free($2);
}
| NUMERAL_TOK DEC_BASED_NUMBER
{ 
  std::string vals($2);
  $$ = new ASTNode(GlobalParserInterface->CreateBVConst(vals, 10, $1));
  free($2);
}
| NUMERAL_TOK HEX_BASED_NUMBER 
{ 
  std::string vals($2);
  $$ = new ASTNode(GlobalParserInterface->CreateBVConst(vals, 16, $1));
  free($2);
}
|      Expr '[' Expr ']' 
{                        
  // valuewidth is same as array, indexwidth is 0.
  unsigned int width = $1->GetValueWidth();
  ASTNode * n = new ASTNode(GlobalParserInterface->nf->CreateTerm(READ, width, *$1, *$3));
  $$ = n;

  delete $1;
  delete $3;
}
|      Expr '(' Expr ')' //array read but in the form of a uninterpreted function application
{
  // valuewidth is same as array, indexwidth is 0.
  unsigned int width = $1->GetValueWidth();
  ASTNode * n = new ASTNode(GlobalParserInterface->nf->CreateTerm(READ, width, *$1, *$3));
  $$ = n;

  delete $1;
  delete $3;
}
|      Expr '[' NUMERAL_TOK ':' NUMERAL_TOK ']' 
{
  int width = $3 - $5 + 1;
  if (width < 0)
    yyerror("Negative width in extract");
                         
  if((unsigned)$3 >= $1->GetValueWidth())
    yyerror("Parsing: Wrong width in BVEXTRACT\n");

  ASTNode hi  =  GlobalParserInterface->CreateBVConst(32, $3);
  ASTNode low =  GlobalParserInterface->CreateBVConst(32, $5);
  ASTNode * n = new ASTNode(GlobalParserInterface->nf->CreateTerm(BVEXTRACT, width, *$1,hi,low));
  $$ = n;
  delete $1;
}
|      BVNEG_TOK Expr 
{
  unsigned int width = $2->GetValueWidth();
  ASTNode * n = new ASTNode(GlobalParserInterface->nf->CreateTerm(BVNOT, width, *$2));
  $$ = n;
  delete $2;
}
|      Expr BVAND_TOK Expr 
{
  unsigned int width = $1->GetValueWidth();
  if (width != $3->GetValueWidth()) {
    yyerror("Width mismatch in AND");
  }
  ASTNode * n = new ASTNode(GlobalParserInterface->nf->CreateTerm(BVAND, width, *$1, *$3));
  $$ = n;
  delete $1;
  delete $3;
}
|      Expr BVOR_TOK Expr 
{
  unsigned int width = $1->GetValueWidth();
  if (width != $3->GetValueWidth()) {
    yyerror("Width mismatch in OR");
  }
  ASTNode * n = new ASTNode(GlobalParserInterface->nf->CreateTerm(BVOR, width, *$1, *$3)); 
  $$ = n;
  delete $1;
  delete $3;
}
|      BVXOR_TOK '(' Expr ',' Expr ')' 
{
  unsigned int width = $3->GetValueWidth();
  if (width != $5->GetValueWidth()) {
    yyerror("Width mismatch in XOR");
  }
  ASTNode * n = new ASTNode(GlobalParserInterface->nf->CreateTerm(BVXOR, width, *$3, *$5));
  $$ = n;
  delete $3;
  delete $5;
}
|      BVNAND_TOK '(' Expr ',' Expr ')' 
{
  unsigned int width = $3->GetValueWidth();
  if (width != $5->GetValueWidth()) {
    yyerror("Width mismatch in NAND");
  }
  ASTNode * n = new ASTNode(GlobalParserInterface->nf->CreateTerm(BVNAND, width, *$3, *$5));
  $$ = n;

  delete $3;
  delete $5;
}
|      BVNOR_TOK '(' Expr ',' Expr ')' 
{
  unsigned int width = $3->GetValueWidth();
  if (width != $5->GetValueWidth()) {
    yyerror("Width mismatch in NOR");
  }
  ASTNode * n = new ASTNode(GlobalParserInterface->nf->CreateTerm(BVNOR, width, *$3, *$5));
  $$ = n;

  delete $3;
  delete $5;
}
|      BVXNOR_TOK '(' Expr ',' Expr ')' 
{
  unsigned int width = $3->GetValueWidth();
  if (width != $5->GetValueWidth()) {
    yyerror("Width mismatch in NOR");
  }
  ASTNode * n = new ASTNode(GlobalParserInterface->nf->CreateTerm(BVXNOR, width, *$3, *$5));
  $$ = n;

  delete $3;
  delete $5;
}
|      BVSX_TOK '(' Expr ',' NUMERAL_TOK ')'
{
  //width of the expr which is being sign
  //extended. $5 is the resulting length of the
  //sign-extended expr
  BVTypeCheck(*$3);
  ASTNode width = GlobalParserInterface->CreateBVConst(32,$5);
  ASTNode *n =
    new ASTNode(GlobalParserInterface->nf->CreateTerm(BVSX, $5,*$3,width));
  $$ = n;
  delete $3;
}
|      BVZX_TOK '(' Expr ',' NUMERAL_TOK ')'
{
  //width of the expr which is being zero
  //extended. $5 is the resulting length of the
  //zero-extended expr
  BVTypeCheck(*$3);
  ASTNode width = GlobalParserInterface->CreateBVConst(32,$5);
  ASTNode *n =
    new ASTNode(GlobalParserInterface->nf->CreateTerm(BVZX, $5,*$3,width));
  $$ = n;
  delete $3;
}
|      Expr BVCONCAT_TOK Expr 
{
  unsigned int width = $1->GetValueWidth() + $3->GetValueWidth();
  ASTNode * n = new ASTNode(GlobalParserInterface->nf->CreateTerm(BVCONCAT, width, *$1, *$3));
  $$ = n;
                         
  delete $1;
  delete $3;
}
|      Expr BVLEFTSHIFT_TOK NUMERAL_TOK 
{
  if (0 == $3)
  	{
  	$$ = $1;
  	}
  else
  {
  ASTNode zero_bits = GlobalParserInterface->CreateZeroConst($3);
  ASTNode * n = 
    new ASTNode(GlobalParserInterface->nf->CreateTerm(BVCONCAT,
                                     $1->GetValueWidth() + $3, *$1, zero_bits));
  $$ = n;
  delete $1;
  }
}
|      Expr BVLEFTSHIFT_TOK Expr
{
  // VARIABLE LEFT SHIFT
  //
  // $1 (THEEXPR) is being shifted
  //
  // $3 is the variable shift amount
  unsigned int width = $1->GetValueWidth();
  ASTNode * ret = new ASTNode(GlobalParserInterface->nf->CreateTerm(BVLEFTSHIFT, width, *$1, *$3));
  BVTypeCheck(*ret);
  //cout << *ret;

  $$ = ret;
  delete $1;
  delete $3;
}
|      Expr BVRIGHTSHIFT_TOK NUMERAL_TOK
{
  ASTNode len = GlobalParserInterface->CreateZeroConst($3);
  unsigned int w = $1->GetValueWidth();

  //the amount by which you are rightshifting
  //is less-than/equal-to the length of input
  //bitvector
  if((unsigned)$3 < w) {
    ASTNode hi = GlobalParserInterface->CreateBVConst(32,w-1);
    ASTNode low = GlobalParserInterface->CreateBVConst(32,$3);
    ASTNode extract = GlobalParserInterface->nf->CreateTerm(BVEXTRACT,w-$3,*$1,hi,low);
    ASTNode * n = new ASTNode(GlobalParserInterface->nf->CreateTerm(BVCONCAT, w,len, extract));
    $$ = n;
  }
  else
    $$ = new ASTNode(GlobalParserInterface->CreateZeroConst(w));

  delete $1;
}
|      Expr BVRIGHTSHIFT_TOK Expr
{
  // VARIABLE RIGHT SHIFT
  //
  // $1 (THEEXPR) is being shifted
  //
  // $3 is the variable shift amount
  unsigned int width = $1->GetValueWidth();
  ASTNode * ret = new ASTNode(GlobalParserInterface->nf->CreateTerm(BVRIGHTSHIFT, width, *$1, *$3));
  BVTypeCheck(*ret);
  //cout << *ret;

  $$ = ret;
  delete $1;
  delete $3;
}
|      BVSHL_TOK '(' Expr ',' Expr ')'
{
  unsigned int width = $3->GetValueWidth();
  ASTNode * n = new ASTNode(GlobalParserInterface->nf->CreateTerm(BVLEFTSHIFT, width, *$3, *$5));
  $$ = n;

  delete $3;
  delete $5;
}
|      BVLSHR_TOK '(' Expr ',' Expr ')'
{
  unsigned int width = $3->GetValueWidth();
  ASTNode * n = new ASTNode(GlobalParserInterface->nf->CreateTerm(BVRIGHTSHIFT, width, *$3, *$5));
  $$ = n;

  delete $3;
  delete $5;
}
|      BVASHR_TOK '(' Expr ',' Expr ')'
{
  unsigned int width = $3->GetValueWidth();
  ASTNode * n = new ASTNode(GlobalParserInterface->nf->CreateTerm(BVSRSHIFT, width, *$3, *$5));
  $$ = n;

  delete $3;
  delete $5;
}
|      BVPLUS_TOK '(' NUMERAL_TOK ',' Exprs ')' 
{
  ASTNode * n = new ASTNode(GlobalParserInterface->nf->CreateTerm(BVPLUS, $3, *$5));
  $$ = n;

  delete $5;
}
|      BVSUB_TOK '(' NUMERAL_TOK ',' Expr ',' Expr ')' 
{
  ASTNode * n = new ASTNode(GlobalParserInterface->nf->CreateTerm(BVSUB, $3, *$5, *$7));
  $$ = n;

  delete $5;
  delete $7;
}
|      BVUMINUS_TOK '(' Expr ')' 
{
  unsigned width = $3->GetValueWidth();
  ASTNode * n =  new ASTNode(GlobalParserInterface->nf->CreateTerm(BVUMINUS,width,*$3));
  $$ = n;
  delete $3;
}
|      BVMULT_TOK '(' NUMERAL_TOK ',' Expr ',' Expr ')' 
{
  ASTNode * n = new ASTNode(GlobalParserInterface->nf->CreateTerm(BVMULT, $3, *$5, *$7));
  $$ = n;

  delete $5;
  delete $7;
}
|      BVDIV_TOK '(' NUMERAL_TOK ',' Expr ',' Expr ')' 
{
  ASTNode * n = new ASTNode(GlobalParserInterface->nf->CreateTerm(BVDIV, $3, *$5, *$7));
  $$ = n;

  delete $5;
  delete $7;
}
|      BVMOD_TOK '(' NUMERAL_TOK ',' Expr ',' Expr ')' 
{
  ASTNode * n = new ASTNode(GlobalParserInterface->nf->CreateTerm(BVMOD, $3, *$5, *$7));
  $$ = n;

  delete $5;
  delete $7;
}
|      SBVDIV_TOK '(' NUMERAL_TOK ',' Expr ',' Expr ')' 
{
  ASTNode * n = new ASTNode(GlobalParserInterface->nf->CreateTerm(SBVDIV, $3, *$5, *$7));
  $$ = n;

  delete $5;
  delete $7;
}
|      SBVREM_TOK '(' NUMERAL_TOK ',' Expr ',' Expr ')' 
{
  ASTNode * n = new ASTNode(GlobalParserInterface->nf->CreateTerm(SBVREM, $3, *$5, *$7));
  $$ = n;
  delete $5;
  delete $7;
}        
|      IfExpr { $$ = $1; }
|      ArrayUpdateExpr
|      LET_TOK LetDecls IN_TOK Expr
{
  $$ = $4;
} | STRING_TOK
{
   cerr << "Unresolved symbol:" << $1 << endl;
   yyerror("bad symbol");
}
;

/*Grammar for Array Update Expr*/
ArrayUpdateExpr : Expr WITH_TOK Updates
{
  ASTNode * result;
  unsigned int width = $1->GetValueWidth();

  ASTNodeMap::iterator it = $3->begin();
  ASTNodeMap::iterator itend = $3->end();
  result = new ASTNode(GlobalParserInterface->nf->CreateArrayTerm(WRITE,
                                            $1->GetIndexWidth(),
                                            width,
                                            *$1,
                                            (*it).first,
                                            (*it).second));
  BVTypeCheck(*result);
  for(it++;it!=itend;it++) {
    result = new ASTNode(GlobalParserInterface->nf->CreateArrayTerm(WRITE,
                                              $1->GetIndexWidth(),
                                              width,
                                              *result,
                                              (*it).first,
                                              (*it).second));
    BVTypeCheck(*result);
  }
  BVTypeCheck(*result);
  $$ = result;
  delete $3;
  delete $1;
}
;

Updates         : '[' Expr ']' ASSIGN_TOK Expr 
{
  $$ = new ASTNodeMap();
  (*$$)[*$2] = *$5;         
  delete $2;
  delete $5;        
}
| Updates WITH_TOK '[' Expr ']' ASSIGN_TOK Expr 
{                   
  (*$1)[*$4] = *$7;
  delete $4;
  delete $7;
}
;

/*Grammar for LET Expr*/
LetDecls        :       LetDecl 
|       LetDecls ',' LetDecl 
;

LetDecl         :       STRING_TOK '=' Expr 
{
  //Expr must typecheck
  BVTypeCheck(*$3);

  //set the valuewidth of the identifier
  
  //populate the hashtable from LET-var -->
  //LET-exprs and then process them:
  //
  //1. ensure that LET variables do not clash
  //1. with declared variables.
  //
  //2. Ensure that LET variables are not
  //2. defined more than once
  GlobalParserInterface->letMgr->LetExprMgr($1,*$3);
  free($1);
  delete $3;
}
|       STRING_TOK ':' Type '=' Expr
{
  //do type checking. if doesn't pass then abort
  BVTypeCheck(*$5);
                          
  if($3.indexwidth != $5->GetIndexWidth())
    yyerror("Fatal Error: parsing: LET Expr: Type check fail: ");
  if($3.valuewidth != $5->GetValueWidth())
    yyerror("Fatal Error: parsing: LET Expr: Type check fail: ");

  GlobalParserInterface->letMgr->LetExprMgr($1,*$5);
  free( $1);
  delete $5;
}
|       STRING_TOK '=' Formula
{
  //Expr must typecheck
  BVTypeCheck(*$3);

  //Do LET-expr management
  GlobalParserInterface->letMgr->LetExprMgr($1,*$3);
  free( $1);
  delete $3;
}
|       STRING_TOK ':' Type '=' Formula
{
  //do type checking. if doesn't pass then abort
  BVTypeCheck(*$5);

  if($3.indexwidth != $5->GetIndexWidth())
    yyerror("Fatal Error: parsing: LET Expr: Type check fail: ");
  if($3.valuewidth != $5->GetValueWidth())
    yyerror("Fatal Error: parsing: LET Expr: Type check fail: ");

  //Do LET-expr management
  GlobalParserInterface->letMgr->LetExprMgr($1,*$5);
  free( $1);
  delete $5;
}                
;

%%

namespace stp {
  int CVCParse(void* AssertsQuery) {
    GlobalParserInterface->letMgr->frameMode = false;
    return cvcparse(AssertsQuery);
  }
}

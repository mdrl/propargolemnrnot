%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Author: Jose Santos <jcas81@gmail.com>
% Date: 2009-03-09
%
%
%    This file contains predicates to generate the bottom clause from the mode declarations
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(bottom_clause,
            [
              % "normal" variablized bottom clauses
              sat/1,  % display only
              sat/2,  % display only but with custom recall

              sat/3,  % compute
              sat/4,  % compute with custom recall

              % ground versions of the bottom clause
              ground_sat/1, % display only
              ground_sat/2, % display only but with custom recall

              ground_sat/3, % compute
              ground_sat/4, % compute with custom recall

	      parallel_sat/6, % added by Miha Drole
	      parallel_sat/7, % added by Miha Drole
	      parsatcache/7,
		  getFromCache/8
            ]
         ).

% GILPS modules
:- use_module('../settings/settings', [setting/2]).  % because of 'i': number of new variables layers, depth and resolutions
:- use_module('../utils/clause', [buildPredCall/4, atomArgsTyped/4, prettyPrintLiterals/1, signature2PredArity/2, skolemize/2]).
:- use_module('../examples/examples', [example/5, positiveExamplesUnifying/4]). % to retrieve example id
:- use_module('../mode declarations/mode_declarations', [mode_head/1, modebDecls/1, recursive_mode_declarations/1]).
:- use_module('../utils/list', [createList/3, split/4, member/2, append/3]).
:- use_module('../utils/control', [uniqueInterpretations/3]).
:- use_module('../engine/propargolem', [is_clp_predicate/1]).


% YAP modules
:- use_module(library(rbtrees)).
:- use_module(library(lists), [member/2, memberchk/2, reverse/2, append/3]).
:- use_module(library(apply_macros), [selectlist/3]).
:- use_module(library(bhash), [b_hash_new/1, b_hash_lookup/3, b_hash_update/4, b_hash_insert/4, b_hash_insert_new/4]).% in the process of replacing rb_trees by bhashes

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Type of important datastructures for constructing the bottom clause.
%
%    InTerms: an rb_tree where the key is a tuple (Term,Type) and value doesn't matter (is [])
%
%    TermsHash: an rb_tree where the key is a tuple (Term,Type) and value is the Variable
%               assigned to Term  (it didn't pay off to use a b_hash, it was slower about 5-10% slower)
%
%    UsedPredCalls: This datastructure is used to know if a given predicate call for a given
%                   predicate signature already appears in the bottom clause.
%
%                   It's a b_hash (an hashtable) where the key is the predicate call and value are signatures
%                   that have been used for that predicate call.
%                   Predicate Call has the input variables ground to constants from BK.
%                   The other constants in call have been ground with skolemize/2
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                             Predicates to manipulate InTerms
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% add2InTerms(+(Term/Type), +InTerms, -NewInTerms)
%
% Given:
%   Term/Type: a term and a type
%   InTerms: Input Terms (see definition above)
%
% Returns:
%   NewInTerms: If Term/Type already exists in InTerms returns InTerms
%               otherwise adds tuple (Term, Type) to InTerms
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

add2InTerms((Term/Type), InTerms, InTerms):- 
  inInTerms(Term/Type, InTerms), !.
add2InTerms((Term/Type), InTerms, NInTerms):- 
  rb_insert(InTerms, (Term/Type), [], NInTerms).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% inInTerms(+(Term/Type), +InTerms)
%
% Given:
%   Term/Type: a term and a type
%   InTerms: Input Terms (see definition above)
%
% Succeeds if Term/Type occurs in InTerms
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

inInTerms((Term/Type), InTerms):-
  rb_lookup((Term/Type), _, InTerms).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% allTermsInInTerms(+ListTermType, +InTerms)
%
% Given:
%   ListTermType: a list of (Term/Type) terms
%   InTerms: Input Terms (see definition above)
%
% Succeeds if all ListTermTypes occur in InTerms
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

allTermsInInTerms([], _).
allTermsInInTerms([H|T], InTerms):-
  inInTerms(H, InTerms),
  allTermsInInTerms(T, InTerms).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% termOfType(+Type, +InTerms, -Term)
%
% Given:
%   Type: data type (e.g. int)
%   InTerms: input terms data structure
%
% Returns:
%   Term: a term from InTerms with type Type
%
% Notes:
%   In backtracking we return all terms. This predicate is not being used anymore. It was
%   only used in bindInputVariables/3 and an equivalent version is coded there that handles
%   commutative predicates.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/*
termOfType(Type, InTerms, Term):-
  rb_visit(InTerms, AllPairs),      % although this two stage test looks heavy, the YAP profiler
  member((Term/Type)-[], AllPairs). % shows it does not matter
*/

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% initialInTerms(-InTerms)
%
% Returns:
%   InTerms: initial Input Terms
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

initialInTerms(InTerms):-
  rb_new(InTerms).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                             Predicates to manipulate TermsHash
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% termToVariable(+(Term/Type), +TermsHash, -Var, -NewTermsHash)
%
% Given:
%   Term/Type: a term and a type
%   TermsHash: a terms hash (see definition above)
%
% Returns:
%   Var: the variable in TermsHash with term Term and type Type
%        or creates a new variable if it does not exist
%   NewTermsHash: TermsHash if Term/Type exists in TermHash, otherwise adds
%                 Term/Type to TermsHash along with a new variable for Term
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

termToVariable(Term/Type, TermsHash, Var, NTermsHash):- 
  (rb_lookup((Term,Type), Var, TermsHash) ->
     NTermsHash=TermsHash
   ;
    rb_insert(TermsHash, (Term,Type), Var, NTermsHash)
  ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% initialTermsHash(-TermsHash)
%
% Returns:
%   TermsHash: initial TermsHash
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

initialTermsHash(TermsHash):-
  rb_new(TermsHash).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                         Predicates to manipulate UsedPredCalls                             %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% initialUsedPredCalls(-UsedPredCalls)
%
% Returns:
%   UsedPredCalls: initial UsedPredCalls
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

initialUsedPredCalls(UsedPredCalls):-
  rb_new(UsedPredCalls).
  %b_hash_new(UsedPredCalls).

% Miha Drole
initUsedPredCalls( [], []).
initUsedPredCalls( [Example | Examples], [Nrb| Orb]) :-
    initialUsedPredCalls(Nrb),
    initUsedPredCalls( Examples, Orb).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% add2UsedPredCalls(+PredSig, +PredCall, +UsedPredCalls, -NUsedPredCalls)
%
% Given:
%   PredSig: Predicate signature (e.g. f(+int,-int)) 
%   PredCall: Predicate call (e.g. f(5, X))
%   UsedPredCalls: UsedPredCalls datastructure
%
% Returns:
%   NUsedPredCalls: Updated UsedPredCalls datastructure with PredSig added as a value for PredCall
%
% Notes:
%   It's guaranteed that the PredSig we are adding doesn't already exist for PredCall.
%   The PredCall we add may even fail but that's not a problem and is worth storing it to avoid
%   evaluating it later
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

add2UsedPredCalls(PredSig, PredCall, UsedPredCalls, NUsedPredCalls):-
  numbervars(PredCall, 0, _),
  %format("Adding ~w with signature ~w~n", [PredCall, PredSig]),
  (rb_update(UsedPredCalls, PredCall, Sigs, [PredSig|Sigs], NUsedPredCalls) -> 
%    format("~w already exists~n",[PredCall]),
    true %PredCall already exists, add signature
   ;
    %does not exist, add it
%    format("~w does not exist~n",[PredCall]),
    rb_insert(UsedPredCalls, PredCall, [PredSig], NUsedPredCalls)
   ).
/* Note: When floats are part of the key, b_hash will not recognize it is the same predicate call
  (b_hash_update(UsedPredCalls, PredCall, Sigs, [PredSig|Sigs]) ->
     format("~w already exists~n",[PredCall]),
     NUsedPredCalls=UsedPredCalls %PredCall already exists, add signature
   ;
     format("~w does not exist~n",[PredCall]),
     b_hash_insert_new(UsedPredCalls, PredCall, [PredSig], NUsedPredCalls) %does not exist, add it
  ).
*/
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% not_already_called(+Predicate Signature, +Predicate Call, +UsedPredCalls)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

not_already_called(PredSignature, PredCall, UsedPredCalls):-
  skolemize(PredCall, PredCall1),
  %rbtrees:rb_size(UsedPredCalls, NumPredCalls),
  %format("Testing if ~w has been called before. Signature: ~w. RBSize:~w~n", [PredCall1, PredSignature, NumPredCalls]),
  (rb_lookup(PredCall1, PredSigs, UsedPredCalls)->
  %(b_hash_lookup(PredCall1, PredSigs, UsedPredCalls) ->
    \+memberchk(PredSignature, PredSigs) %succeed only if PredSignature does not occur in PredSigs
  ; true). % if PredCall1 does not exist then succeed!
  %format("it was not called~n", [PredCall1, PredSignature]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% generalizeLiteral(+Mode, +Signature, +Literal, +InTerms, +TermsHash, +LiteralSource,
%                   -GeneralizedLiteral, -NewInTerms, -NewTermsHash)
%
% Given:
%   Mode: bottom clause generation mode, either 'mode(ground, Recall)' or 'mode(variablized, Recall)'
%   Signature: signature of a literal (e.g. a(+char,-int,#class))
%   Literal: ground literal (e.g. (a(c,5,mammal)))
%   InTerms: as described above. E.g. []
%   TermsHash: as described above. E.g. []
%   LiteralSource: either head or body.
%
% Returns:
%   GeneralizedLiteral: Literal generalized (e.g. (a(A,B,mammal)))
%   NewInTerms: InTerms after processing this literal. E.g. [(5,int), (c/char)]
%   TermsHash: TermsHash after processing this literal. E.g. [(5,int,B), (c, char,A)]
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

generalizeLiteral(Mode, Signature, GroundLit, InTerms, TermsHash, LiteralSource,
                  GeneralizedLiteral, NewInTerms, NewTermsHash):-
  Signature=..[PredName|SigArgs],
  GroundLit=..[PredName|LitArgs],
  %processLiteralArgs(SigArgs, LitArgs, InTerms, TermsHash, LiteralSource, Args, NewInTerms, NewTermsHash),% we could 
  (Mode=mode(ground, _Recall) ->
    skipLiteralArgs(SigArgs, LitArgs, InTerms, NewInTerms),  % this is equivalent to call processLiteralArgs/6 but ~25% faster since we don't update TermsHash
    NewTermsHash=TermsHash, % TermsHash is not updated in ground bottom clauses
    GeneralizedLiteral=GroundLit
   ; %Mode=mode(variablized, _Recall)
    processLiteralArgs(SigArgs, LitArgs, InTerms, TermsHash, LiteralSource, Args, NewInTerms, NewTermsHash),
    GeneralizedLiteral=..[PredName|Args]
  ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% skipLiteralArgs(+SigArgs, +LitArgs, +InTerms, -NewInTerms)
%
% skipLiteralArgs/4 should only be used when we are constructing a ground bottom clause. It is identical to processLiteralArgs but does not update termsHash
% (the datastructure that associates variables to terms) nor constructs generalized args because they are not needed for a ground bottom clause.
%
% Apart from this, it is identical to processLiteralArgs/8 (for WorkingMode='body')
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

skipLiteralArgs([], [], InputTerms, InputTerms).
skipLiteralArgs([#_Type|SigArgs], [_Term|LitArgs], InTerms, NInputTerms):-
  !,
  skipLiteralArgs(SigArgs, LitArgs, InTerms, NInputTerms).
skipLiteralArgs([+Type|SigArgs], [Term|LitArgs], InTerms, NInputTerms):-
  !,
  add2InTerms(Term/Type, InTerms, InTerms1),
  skipLiteralArgs(SigArgs, LitArgs, InTerms1, NInputTerms).
skipLiteralArgs([-Type|SigArgs], [Term|LitArgs], InTerms, NInputTerms):-
  !,
  add2InTerms(Term/Type, InTerms, InTerms1),
  skipLiteralArgs(SigArgs, LitArgs, InTerms1, NInputTerms).
skipLiteralArgs([ComplexType|SigArgs], [ComplexTerm|LitArgs], InTerms, NInputTerms):-
  !,
  ComplexType=..[ComplexTermName|ComplexTermSigs],
  ComplexTerm=..[ComplexTermName|ComplexTermArgs],
  skipLiteralArgs(ComplexTermSigs, ComplexTermArgs, InTerms, InTerms1),
  skipLiteralArgs(SigArgs, LitArgs, InTerms1, NInputTerms).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% processLiteralArgs(+SigArgs, +LitArgs, +InTerms, +TermsHash, +WorkingMode, -Args, -NewInTerms, -NewTermsHash)
%
% Given:
%   SigArgs: list of signature arguments. E.g.: [+char,-int,#class])
%   LitArgs: list of ground literal argumens. E.g.: [c,5,mammal]
%   InTerms: as described above. E.g. []
%   TermsHash: as described above. E.g. []
%   WorkingMode: either head or body. The only difference between the two modes is that in the latter
%      variables of -type add added to InTerms
%
% Returns:
%   Args: arguments according to the signature and LitArgs. E.g.: [A,B,mammal].
%   NewInTerms: InTerms after processing this literal. E.g. [(5,int), (c/char)]
%   TermsHash: TermsHash after processing this literal. E.g. [(5,int,B), (c, char,A)]
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

processLiteralArgs([], [], InputTerms, TermsHash, _, [], InputTerms, TermsHash).
processLiteralArgs([#_Type|SigArgs], [Term|LitArgs], InTerms, TermsHash, WM, [Term|Args], NInputTerms, NTermsHash):-
  !,
  processLiteralArgs(SigArgs, LitArgs, InTerms, TermsHash, WM, Args, NInputTerms, NTermsHash).
processLiteralArgs([+Type|SigArgs], [Term|LitArgs], InTerms, TermsHash, WM, [Var|Args], NInputTerms, NTermsHash):-
  !,
  add2InTerms(Term/Type, InTerms, InTerms1),
  termToVariable(Term/Type, TermsHash, Var, TermsHash1),
  processLiteralArgs(SigArgs, LitArgs, InTerms1, TermsHash1, WM, Args, NInputTerms, NTermsHash).
processLiteralArgs([-Type|SigArgs], [Term|LitArgs], InTerms, TermsHash, WM, [Var|Args], NInputTerms, NTermsHash):-
  !,
  termToVariable(Term/Type, TermsHash, Var, TermsHash1),
  (WM=head->
    InTerms1=InTerms
  ;%WM=body
    add2InTerms(Term/Type, InTerms, InTerms1)),
  processLiteralArgs(SigArgs, LitArgs, InTerms1, TermsHash1, WM, Args, NInputTerms, NTermsHash).
processLiteralArgs([ComplexType|SigArgs], [ComplexTerm|LitArgs], InTerms, TermsHash, WM, [ComplexArg|Args], NInputTerms, NTermsHash):-
  !,
  ComplexType=..[ComplexTermName|ComplexTermSigs],
  ComplexTerm=..[ComplexTermName|ComplexTermArgs],
  processLiteralArgs(ComplexTermSigs, ComplexTermArgs, InTerms, TermsHash, WM, ComplexArgs, InTerms1, TermsHash1),
  ComplexArg=..[ComplexTermName|ComplexArgs],
  processLiteralArgs(SigArgs, LitArgs, InTerms1, TermsHash1, WM, Args, NInputTerms, NTermsHash).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% createHead(+Example, +Mode, +HeadSignature, -Head, -InputTerms, -TermsHash)
%
% Given:
%   Example: example used to construct head
%   Mode: bottom clause generation mode, either 'mode(ground, Recall)' or 'mode(variablized, Recall)'
%   HeadSignature: the signature of the head (and example)
%
% Returns:
%   Head: the generalized head for the bottom clause (from example and head signature)
%   InputTerms: Input terms from the head of the bottom clause (i.e. extracted from the example)
%   TermsHash: Terms Hash from all the terms in the example
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

createHead(Example, Mode, HeadSignature, Head, InputTerms, TermsHash):-
  initialInTerms(InitInTerms),
  initialTermsHash(InitTermsHash),
  generalizeLiteral(Mode, HeadSignature, Example, InitInTerms, InitTermsHash, head, Head, InputTerms, TermsHash).

% Miha Drole
createHeads([], _, _, [], [], []).
createHeads([Example | Examples], Mode, HeadSignature, [Head | Heads], [InputTerms | OtherInputTerms], [TermsHash | OtherTermsHash]) :-
    createHead(Example, Mode, HeadSignature, Head, InputTerms, TermsHash),
    createHeads(Examples, Mode, HeadSignature, Heads, OtherInputTerms, OtherTermsHash).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% createBody(+Example, +Mode, +InputTerms, +TermsHash, +Mode, -Body, -BodySignature)
%
% Given:
%   Example: example used to construct body (only used if body is recursive or bottom_early_stop=true)
%   Mode: bottom clause generation mode, either 'mode(ground, Recall)' or 'mode(variablized, Recall)'
%   InputTerms: Input terms from the head of the bottom clause (i.e. extracted from the example)
%   TermsHash: Terms Hash from all the terms in the example
%
% Returns:
%   Body: a list of literals, the body of the bottom clause (in reversed form)
%   BodySignature: for each body literal it's modeb signature (in normal form)
%   FTermsHash: final terms hash for all the terms in body and example
%
% Notes:
%   Example is only used in createBody if the clause is recursive and we need to check that we
%   do not add the example itself to the bottom clause
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

createBody(Example, Mode, InputTerms, TermsHash, Body, BodySignature):-
  modebDecls(ModeBDecls),
  initialUsedPredCalls(UsedPredCalls),
  initialVarLayer(Example, InputTerms, InitVarLayer),
  createBody(InitVarLayer, Mode, Example, ModeBDecls, UsedPredCalls, InputTerms, TermsHash, [], Body, BodySignature).

%createBody(+CurVarLayer, +GenMode, +Example, +ModeBDecls, +UsedPredCalls, +InputTerms, +TermsHash, +CurBody, -FinalBody, -BodySignature)

createBody(0, _GenMode, _Example, _ModeBDecls, _UsedPredCalls, _InputTerms, _TermsHash, Body, Body, []):-!.
createBody(CurVarLayer, GenMode, Example, ModeBDecls, UsedPredCalls, InTerms, TermsHash, CurBody, FinalBody, BodySignature):-
  createBodyAtVarDepth(ModeBDecls, GenMode, Example, CurBody, InTerms, UsedPredCalls, InTerms, TermsHash,
                       NBody, NUsedPredCalls, NInTerms, NTermsHash, CurBodySignature),
  append(CurBodySignature, NBodySignature, BodySignature), %append the body signature
  updateVarLayer(CurVarLayer, Example, NInTerms, NextVarLayer),
  createBody(NextVarLayer, GenMode, Example, ModeBDecls, NUsedPredCalls, NInTerms, NTermsHash, NBody, FinalBody, NBodySignature).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% initialVarLayer(+Example, +InTerms, -InitVarLayer)
%
% Given:
%   Example: example used to construct body (we are interested in extracting the list of output (Term/Type) terms from it)
%   InTerms: InTerms available at the beginning
%
% Returns:
%   InitVarLayer: Initial variable layer
%
% Notes:
%   The initial var layer is normally 'i', unless bottom_early_stop occurs in which case it's 0 (i.e. do not construct anything)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

initialVarLayer(Example, InTerms, InitVarLayer):-
  (bottom_early_stop(Example, InTerms)->
    InitVarLayer=0
   ;
    setting(i, InitVarLayer)
  ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% updateVarLayer(+CurVarLayer, +Example, +InTerms, -NextVarLayer)
%
% Given:
%   CurVarLayer: current variable layer 
%   Example: example used to construct body (we are interested in extracting the list of output (Term/Type) terms from it)
%   InTerms: InTerms available for next iteration
%
% Returns:
%   NextVarLayer: the next variable layer
%
% Notes:
%   The next variable layer is either CurVarLayer-1 or 0. It's 0 if CurVarLayer=1 or if bottom_early_stop(Example, InTerms) succeeds
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

updateVarLayer(CurVarLayer, Example, InTerms, NextVarLayer):-
  (bottom_early_stop(Example, InTerms)->
    NextVarLayer=0
  ;
    NextVarLayer is CurVarLayer-1
  ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% bottom_early_stop(+Example, +InTerms)
%
% Given:
%   Example: example used to construct body (we are interested in extracting the list of output (Term/Type) terms from it)
%   InTerms: InTerms available for next iteration
%
% Notes:
%   Example is just used to extract the list of output terms from it. It would be more reliable to provide them directly.
%   Note that we have to access mode_head/1 in order to access the Example signature. This is not good practice and will
%   cause problems if in the future we allow several modeh at the same time. This is easy to fix but requires passing
%   even more parameters to the already parameter crowded createBody predicate.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

bottom_early_stop(Example, InTerms):-
  setting(bottom_early_stop, true),
  mode_head(Head_Signature),
  atomArgsTyped(Example, Head_Signature, _, HeadOutputTermsTypes),
  HeadOutputTermsTypes=[_|_],% only test allTermsInInTerms if there is at least one output term type, otherwise behave as if bottom_early_stop=false
  allTermsInInTerms(HeadOutputTermsTypes, InTerms).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% createBodyAtVarDepth(+ModeBDecls, +GenMode, +Example, +CurBody, +InitialInputTerms, +UsedPredCalls, +CurInputTerms, +CurTermsHash,
%                      -NextBody, -NUsedPredCalls, -NInTerms, -NTermsHash, -BodySignature)
%
% Given:
%   ModeBDecls: list of mode body declarations
%   GenMode: bottom clause generation mode, either 'mode(ground, Recall)' or 'mode(variablized, Recall)'
%   Example: example used to construct the current clause (only used if clause is recursive)
%   CurBody: the current body of the bottom clause (with generalized literals)
%   InitialInputTerms: input terms allowed at this variable depth
%   UsedPredCalls: used predicate calls, a list of pairs (predsignature, predcall),
%                  with predcall having the input variables instantiated, and the free variables ground with numbervars
%   CurInputTerms: current input terms
%   CurTerms: current terms hash
%
% Returns:
%   NextBody: the body of the bottom clause after all modebdecls have been processed
%   NUsedPredCalls: updated used predicate calls after processing all modebdecls
%   NCurInTerms: updated input terms after processing all modebdecls
%   NTermsHash: updated terms hash after processing all modebdecls
%   BodySignature: the signature of all literals in NextBody
%
% Notes:
%   In the initial call, InitialInputTerms and CurInputTerms are the same. We need to pass them as two separate
%   parameters because all mode body declarations at the same level should only see the same input terms, we
%   shouldn't use newly added input terms for later mode body declarations of the same level
%
%   UsedPredCalls is here to make sure we don't add repeated literals to the bottom clause
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

createBodyAtVarDepth([], _GenMode, _Example, Body, _InitInTerms, UPCalls, InTerms, TermsHash, Body, UPCalls, InTerms, TermsHash, []):-!.
createBodyAtVarDepth([modeb(Recall, PredSig, PredInfo)|ModeBDecls], GenMode, Example, CurBody, InitInTerms, UPCalls, InTerms, TermsHash, NBody, NUPCalls, NInTerms, NTermsHash, BodySignature):-
  constructLiteralsForDecl(modeb(Recall, PredSig, PredInfo), GenMode, Example, UPCalls, InitInTerms, InTerms, TermsHash, Literals, UPCalls1, InTerms1, TermsHash1),  
  length(Literals, NumLiterals), % all Literals of a given ModeBDecl have the same signature, ModeBDecl
  createList(NumLiterals, PredSig, LiteralsSignatures), % create literals signatures (i.e. PredSig NumLiterals times)
  append(LiteralsSignatures, NBodySignature, BodySignature),
  append(Literals, CurBody, CurBody1), % we do this rather than append(CurBody, Literals, CurBody1), because CurBody is in general much larger than Literals
  createBodyAtVarDepth(ModeBDecls, GenMode, Example, CurBody1, InitInTerms, UPCalls1, InTerms1, TermsHash1, NBody, NUPCalls, NInTerms, NTermsHash, NBodySignature).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% constructLiteralsForDecl(+ModeBDecl, +GenMode, +Example, +UsedPredCalls, +InitInTerms, +InTerms, +TermsHash,
%                         -Literals, -NUsedPredCalls, -NInTerms, -NTermsHash)
%
% Given:
%   ModeDecl: a mode body declaration. E.g.: modeb(10, atom(+mol, -atomid, -int, #elem), normal).
%   GenMode: bottom clause generation mode, either 'mode(ground, Recall)' or 'mode(variablized, Recall)'
%   Example: example used to construct the actual modebdecl (only used if current modebdecl is the same as modeh)
%   UsedPredCalls: data structure that stores the used predicate calls (to avoid repetited literals in bottom)
%   InitInTerms: available InTerms at this iteration
%   InTerms: current interms (with newly added output variables)
%   TermsHash: TermsHash datastructure described above
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

constructLiteralsForDecl(modeb(Recall, PredSig, PredInfo), GenMode, Example, UsedPredCalls, InitInTerms, InTerms, TermsHash,
                         Literals, NUsedPredCalls, NInTerms, NTermsHash):-
  buildPredCall(PredSig, IOCVars, Types, PredCall),
  findall((PredCall, PredInts), % we want to backtrack through all possible input variable instantiations for PredCall
           (bindInputVariables(Types, PredInfo, InitInTerms, IOCVars), %IOCVars are variables of PredCall, this will instantiate them and backtrack as there may be any different possible instantiations            
            not_already_called(PredSig, PredCall, UsedPredCalls), % check if PredCall has been called before
            predInterpretations(GenMode, Recall, PredCall, Example, PredInts)
           ),
          AllPredInts),% list of pairs (PredCall, list of interpretations for PredCall)
  processInterpretations(AllPredInts, GenMode, PredSig, InTerms, TermsHash, UsedPredCalls, Literals, NInTerms, NTermsHash, NUsedPredCalls).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% predInterpretations(+GenMode, +ModeBRecall, +PredicateToCall, +Example, -PredicateInterpretations)
%
% Given:
%   GenMode: bottom clause generation mode, either 'mode(ground, Recall)' or 'mode(variablized, Recall)'
%   ModeBRecall: number of times to call predicate  (according to mode declaration)
%   PredicateToCall: the predicate to be executed (with at least its input variables instantiated)
%   Example: example used to construct the current bottom clause (only used in recursiveInterpretation)
%
% Returns:
%   PredicateInterpretations: up to Recall interpretations (i.e. solutions) of the execution of PredicateToCall
%
% Notes:
%   If PredCall is recursive we are returning examples from all the folds, thus if cross fold validation is active
%   the resulting theory may perform better than it should in reality (review in the future)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

predInterpretations(mode(_, OverrideRecall), ModeBRecall, PredCall, Example, PredInterpretations):-
  (OverrideRecall=default -> ActualRecall=ModeBRecall ; ActualRecall=OverrideRecall),
  uniqueInterpretations(ActualRecall, PredCall, PredInts), %Each predcall interpretation is a list of ground literals of Pred
  removeExampleFromPredInts(PredInts, Example, PredInterpretations).

%removeExampleFromPredInts(+PredInts, +Example, -FinalPredInts)
removeExampleFromPredInts(PredInts, _, PredInts):-
  recursive_mode_declarations(false),!. % not recursive modes, so no need to check interpretations
removeExampleFromPredInts(PredInts, Example, FPredInts):-
  selectlist(diffTerm(Example), PredInts, FPredInts).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% diffTerm(+Term1, +Term2)
%
% Given:
%   Ground terms Term1 and Term2.
%
% Succeeds if Term1 and Term2 are distinct
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

diffTerm(Term1, Term2):-
  Term1\==Term2.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% processInterpretations(+List(Pred Call, Pred Interpretations), +GenMode, +PredSignature, +InTerms, +TermsHash, +UsedPredCalls,
%                         -GeneralizedLiterals, -NInTerms, -NTermsHash, -NUsedPredCalls)
%
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

processInterpretations([], _GenMode, _PredSig, InTerms, TermsHash, UsedPredCalls, [], InTerms, TermsHash, UsedPredCalls).
processInterpretations([(PredCall, PredInts)|PCallInts], GenMode, PredSig, InTerms, TermsHash, UsedPredCalls,
                       GenLiterals, NInTerms, NTermsHash, NUsedPredCalls):-
  processBodyLiterals(PredInts, GenMode, PredSig, InTerms, TermsHash, GenLits, InTerms1, TermsHash1),
  append(GenLits, TailGenLits, GenLiterals),
  add2UsedPredCalls(PredSig, PredCall, UsedPredCalls, UsedPredCalls1),
  processInterpretations(PCallInts, GenMode, PredSig, InTerms1, TermsHash1, UsedPredCalls1,
                         TailGenLits, NInTerms, NTermsHash, NUsedPredCalls).

% processBodyLiterals(+GroundLits, +GenMode, +PredSig, +InTerms, +TermsHash, -GenLits, -NInTerms, -NTermsHash)
processBodyLiterals([], _GenMode, _PredSig, InTerms, TermsHash, [], InTerms, TermsHash).
processBodyLiterals([GroundLit|GroundLits], GenMode, PredSig, InTerms, TermsHash, [GenLit|GenLits], NInTerms, NTermsHash):-
  generalizeLiteral(GenMode, PredSig, GroundLit, InTerms, TermsHash, body, GenLit, InTerms1, TermsHash1),
  processBodyLiterals(GroundLits, GenMode, PredSig, InTerms1, TermsHash1, GenLits, NInTerms, NTermsHash).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% bindInputVariables(+IOTypes, +PredInfo, +InTerms, ?IOCVars)
%
% Given:
%   IOTypes: list of types and IO modes of IOCVars (e.g. [+int,-int,+char]
%   PredInfo: either 'normal' or 'commutative'
%   InTerms: available input terms list to bind IOCVars to
%   IOCVars: list of free variables (of type Types)
%
% Returns:
%   IOCVars: the free variables that are of IOMode input will be bound, the others (output and constant) will remain free
%
% Notes:
%  This predicate is highly dependant on the structure of InTerms (currently a rb_tree)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

bindInputVariables(IOTypes, PredInfo, InTerms, IOCVars):-
  rb_visit(InTerms, InTermsAsList), % converts InTerms red-black tree to list representation
  bindInputVariablesAux(IOTypes, PredInfo, InTermsAsList, IOCVars).

bindInputVariablesAux([], _, _, []).
bindInputVariablesAux([+Type|IOTypes], PredInfo, InTerms, [Term|IOCVars]):-
  !,
  (PredInfo=normal->
    member((Term/Type)-[], InTerms),
    NInTerms=InTerms
   ;%PredInfo=commutative
    split(InTerms, (Term/Type)-[], Before, After),
    selectlist(diffType(Type), Before, NBefore),  %remove everything in list Before of type Type
    append(NBefore, [(Term/Type)-[]|After], NInTerms)
  ),
  bindInputVariablesAux(IOTypes, PredInfo, NInTerms, IOCVars).
bindInputVariablesAux([_|IOTypes], PredInfo, InTerms, [_|IOCVars]):- %ignore current IOType as it is not input ('+')
  bindInputVariablesAux(IOTypes, PredInfo, InTerms, IOCVars).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% diffType(+IgnoreType, +InTermsTuple)
%
% Given:
%   IgnoreType: type to ignore
%   InTermsTuple: tuple of the form: Term/Type-[]
%
% Succeeds if InTermTuple Type is of a type other than IgnoreType
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%diffType(+Type, +Var/Type-[]).
diffType(Type1, _/Type2-[]):-
  Type1\==Type2.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% bottom_clause(+Example, +Mode, -Clause, -ClauseSig)
%
% Given:
%   Example: an example (e.g. class(dog, mammal))
%   Mode: bottom clause generation mode, either 'mode(ground, Recall)' or 'mode(variablized, Recall)'
%         If 'ground' Clause is all ground, if 'variablized' is a "normal" bottom clause.
%         Recall is either 'default' in which case the default recall from the modebs should be used
%         otherwise is an integer with the recall to use
%
% Returns:
%   BottomClause: the bottom clause for the given example, as a list of literals
%   BottomClauseSignature: predicate signatures for all the literals in bottom clause
%   TermsHash: an hash of the variables associated to all (term,type) in BottomClause
%
% Notes:
%   The example has to match mode_head
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

bottom_clause(Example, Mode, [Head|Body], [Head_Signature|BodySignature]):-
  mode_head(Head_Signature),
  createHead(Example, Mode, Head_Signature, Head, InTerms, Hash),
  createBody(Example, Mode, InTerms, Hash, RBody, BodySignature),
  reverse(RBody, Body). % Body is returned in reversed form, RBody has it in the proper form

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% show_bottom_clause(+ExampleID, +Mode)
%
% Given:
%   ExampleID: an example id (a positive integer, starting from 1)
%   Mode: either 'ground' or 'variablized'. If 'ground' Clause is all ground, if
%         'variablized' is a "normal" bottom clause
%
% Prints to sdout
%   Bottom clause for example ExampleID
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

show_bottom_clause(ExampleID, Mode):-
  example(ExampleID, Example, _, _, _),
  format("Bottom clause for example id ~w, ~k:~2n", [ExampleID, Example]),
  bottom_clause(Example, Mode, BottomClauseLits, _Signature),
  prettyPrintLiterals(BottomClauseLits),
  length(BottomClauseLits, NumLiterals),
  format("~n[Num literals=~w]~n", [NumLiterals]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% ground_sat(+Example, +Recall, -Clause, -ClauseSignature)
%
% Given:
%   Example: an example
%   Recall: the recall to use to construct the bottom clause (Clause) or 'default'
%           to use the recall from the mode definition
%
% Returns:
%  Clause: Ground bottom clause for example with recall Recall
%  ClauseSignature: Clause's signature
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%compute
ground_sat(Example, Clause, ClauseSignature):-
  ground_sat(Example, default, Clause, ClauseSignature).
ground_sat(Example, Recall, Clause, ClauseSignature):-
  bottom_clause(Example, mode(ground, Recall), Clause, ClauseSignature).

% display
ground_sat(ExampleID):-
  ground_sat(ExampleID, default).
ground_sat(ExampleID, Recall):-
  show_bottom_clause(ExampleID, mode(ground, Recall)).

%variablized bottom clause

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% sat(+Example, +Recall, -Clause, -ClauseSignature)
%
% Given:
%   Example: an example
%   Recall: the recall to use to construct the bottom clause (Clause) or 'default'
%           to use the recall from the mode definition
%
% Returns:
%  Clause: Variablized bottom clause for example with recall Recall
%  ClauseSignature: Clause's signature
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%compute
sat(Example, Clause, ClauseSignature):-
  sat(Example, default, Clause, ClauseSignature).
sat(Example, Recall, Clause, ClauseSignature):-
  bottom_clause(Example, mode(variablized, Recall), Clause, ClauseSignature).

%display
sat(ExampleID):-
  sat(ExampleID, default).
sat(ExampleID, Recall):-
  show_bottom_clause(ExampleID, mode(variablized, Recall)).

  
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%   Added by Miha Drole.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%
%
% Compute the parallel saturation of examples Example1 and Example2.
% Entry point.
%
%
parallel_sat(Examples, Sat, SatSig) :-
    parallel_sat(Examples, mode(variablized, default), Sat, SatSig).


% 
parallel_sat(Examples, Mode, GenSat, SatSig) :-
    compute_nwise_bottom_clause(Examples, Mode, Sat, SatSig),
    generalizeClause(SatSig, Sat, Mode, GenSat).


getFromCache([], [], [], [], [], [], [], []).





getFromCache([E|OE], [S|OS], [SS|OSS], [UPC|OUPC], [IT|OIT], [TH|OTH], [AV|OAV], [L | OL]) :-
    getFromCache(OE, OS, OSS, OUPC, OIT, OTH, OAV, OL),
    user:parsatcache(E, S, SS, UPC, IT, TH, AV, L).



compute_nwise_bottom_clause(Examples, Mode, Saturation, SaturationSignature) :-
    getFromCache(Examples, Sats, SatSigs, UsedPredCalls, InputTerms, TermsHash, AppearingVars, Layers),
    Sats = [SeedSat | OtherSats], 
    SatSigs = [SeedSatSig | OtherSatSigs],
    InputTerms = [_ | OtherInputTerms],
    SeedSat = [SeedHead | _],
    SeedSatSig = [SeedHeadSig | _],
    AppearingVars = [SAppearingVars | OtherAppearingVars],
    Layers = [SLayers | _],
    Examples = [SeedExample | _],
    createHead(SeedExample, Mode, SeedHeadSig, SeedHead, SeedInputTerms, SeedTermsHash),
    initialVarLayer(SeedHead, SeedInputTerms, Layer),
    initAppearingVars(SeedHead, SeedHeadSig, SeedAppearingVars),
    litsWithAllMatches(SeedSat, SeedAppearingVars, SeedInputTerms, SeedSatSig, OtherSats, OtherAppearingVars, OtherInputTerms, OtherSatSigs, SLayers, Saturation, SaturationSignature, _).




compute_nwise_bottom_clause(0, _, _, _, _, _, _, _, _, [], []) :- !.



compute_nwise_bottom_clause(Layer, Mode, Examples, ModeBDecls, UsedPredCalls, InputTerms, TermsHash, AppearingVars, StartBodies, BottomClause, BottomClauseSignature) :-
    computeBodySteps(Layer, Mode, Examples, ModeBDecls, UsedPredCalls, InputTerms, TermsHash, StartBodies, ReversedNewBodies, NewUsedPredCalls, NewInTerms, NewTermsHash, NewBodySignatures),
    reverse_all(ReversedNewBodies, NewBodies),
    rb_invert_all(NewTermsHash, InvNewTermsHash),
    NewBodies = [NewSeedBody | OtherNewBodies],
    AppearingVars = [SeedAppearingVars | OtherAppearingVars],
    InputTerms = [SeedInputTerms | OtherInputTerms],
    NewBodySignatures = [NewSeedBodySignature | OtherNewBodySignatures],
    InvNewTermsHash = [NewSeedInvTermsHash | NewOtherInvTermsHashes],
    NewInTerms = [SeedNewInTerms | OtherNewInTerms],
    litsWithAllMatches(NewSeedBody, SeedAppearingVars, SeedInputTerms, NewSeedBodySignature, OtherNewBodies, OtherAppearingVars, OtherInputTerms, OtherNewBodySignatures, Layer, ClauseWithMatches, ClauseWithMatchesSignature, ClauseWithMatchesInTerms), 
    extendAppearingVariables(ClauseWithMatches, ClauseWithMatchesSignature, Layer, SeedAppearingVars, NewAppearingVars),
    extendAppearingVariables_all(OtherNewBodies, OtherNewBodySignatures, Layer, OtherAppearingVars, NewOtherAppearingVars),
    vars_to_terms(ClauseWithMatchesInTerms, NewSeedInvTermsHash, NewSeedInTermsGround),
    vars_to_terms_all(OtherNewInTerms, NewOtherInvTermsHashes, NewOtherInTermsGround),
    NewLayer is Layer - 1,
    compute_nwise_bottom_clause(NewLayer, Mode, Examples, ModeBDecls, NewUsedPredCalls, [NewSeedInTermsGround | NewOtherInTermsGround], NewTermsHash, [NewAppearingVars | NewOtherAppearingVars], [ClauseWithMatches | OtherNewBodies], NextLevelClause, NextLevelSignature),
    append(ClauseWithMatchesSignature, NextLevelSignature, BottomClauseSignature),
    append(ClauseWithMatches, NextLevelClause, BottomClause).



% Same as compute_nwise_bottom_clause, but also returns UsedPredCalls, InputTerms, TermsHash and AppearingVars



compute_nwise_bottom_clause_cache(M, ML , _, _, _, UPC, IT, TH, AV, _, [], [], UPC, IT, TH, AV, []) :- ML < M, !.


compute_nwise_bottom_clause_cache(Layer, MaxLayer, Mode, Examples, ModeBDecls, UsedPredCalls, InputTerms, TermsHash, AppearingVars, StartBodies, BottomClause, BottomClauseSignature, UPC, IT, TH, AV, Layers) :-
    computeBodySteps(Layer, Mode, Examples, ModeBDecls, UsedPredCalls, InputTerms, TermsHash, StartBodies, ReversedNewBodies, NewUsedPredCalls, NewInTerms, NewTermsHash, NewBodySignatures),
    reverse_all(ReversedNewBodies, NewBodies),
    rb_invert_all(NewTermsHash, InvNewTermsHash),
    NewBodies = [NewSeedBody | OtherNewBodies],
    AppearingVars = [SeedAppearingVars | OtherAppearingVars],
    InputTerms = [SeedInputTerms | OtherInputTerms],
    NewBodySignatures = [NewSeedBodySignature | OtherNewBodySignatures],
    InvNewTermsHash = [NewSeedInvTermsHash | NewOtherInvTermsHashes],
    NewInTerms = [SeedNewInTerms | OtherNewInTerms],
    litsWithAllMatches(NewSeedBody, SeedAppearingVars, SeedInputTerms, NewSeedBodySignature, OtherNewBodies, OtherAppearingVars, OtherInputTerms, OtherNewBodySignatures, Layer, ClauseWithMatches, ClauseWithMatchesSignature, ClauseWithMatchesInTerms), 
    extendAppearingVariables(ClauseWithMatches, ClauseWithMatchesSignature, Layer, SeedAppearingVars, NewAppearingVars),
    extendAppearingVariables_all(OtherNewBodies, OtherNewBodySignatures, Layer, OtherAppearingVars, NewOtherAppearingVars),
    vars_to_terms(ClauseWithMatchesInTerms, NewSeedInvTermsHash, NewSeedInTermsGround),
    vars_to_terms_all(OtherNewInTerms, NewOtherInvTermsHashes, NewOtherInTermsGround),
    NewLayer is Layer + 1,
    compute_nwise_bottom_clause_cache(NewLayer, MaxLayer, Mode, Examples, ModeBDecls, NewUsedPredCalls, [NewSeedInTermsGround | NewOtherInTermsGround], NewTermsHash, [NewAppearingVars | NewOtherAppearingVars], [ClauseWithMatches | OtherNewBodies], NextLevelClause, NextLevelSignature, UPC, IT, TH, AV, OtherLayers), 
    append(ClauseWithMatchesSignature, NextLevelSignature, BottomClauseSignature),
    append(ClauseWithMatches, NextLevelClause, BottomClause),
    numList(Layer, ClauseWithMatches, CurrentLayers),
    append(CurrentLayers, OtherLayers, Layers).
    
    






computeBodySteps(_, _, [], _, [], [], [], [], [], [], [], [], []) :- !.

computeBodySteps(Layer, Mode, [Example | Examples], ModeBDecls, [UsedPredCalls | OtherUsedPredCalls], [InputTerms | OtherInputTerms], [TermsHash | OtherTermsHashes], [StartBody | OtherStartBodies], [RNBody | OtherRNBodies], [NUsedPredCalls | OtherNUsedPredCalls], [NInTerms | OtherNInTerms], [NTermsHash | OtherNTermsHashes], [NBodySignature | OtherNBodySignatures]) :- 
    createBodyStep(Layer, Mode, Example, ModeBDecls, UsedPredCalls, InputTerms, TermsHash, StartBody, RNBody, NUsedPredCalls, NInTerms, NTermsHash, NBodySignature),
    computeBodySteps(Layer, Mode, Examples, ModeBDecls, OtherUsedPredCalls, OtherInputTerms,  OtherTermsHashes, OtherStartBodies, OtherRNBodies, OtherNUsedPredCalls, OtherNInTerms, OtherNTermsHashes,  OtherNBodySignatures).



%
%
% litsWithMatches -- remove literals that have no match in the other clause.
%
%

%S - the literals being reduced, O - the literals to match against

litsWithAllMatches([], _, A, _, _, _, _, _, _, [], [], A).

litsWithAllMatches([Lit1 | SLiterals], SAppearingVars, SInputTerms, [Lit1Sig | SLiteralsSigs], OClauses, OAppearingVars, OInputTerms, OClausesSigs, Layer, [Lit1 | NTLiterals], [Lit1Sig | NTSigs], FInTerms) :-
    (Layer = [CurLayer | NLayer] ; CurLayer = Layer, NLayer = Layer),
    hasMatchesInAll(Lit1, SAppearingVars, SInputTerms, Lit1Sig, OClauses, OAppearingVars, OInputTerms, OClausesSigs), !, 
    extendInTerms(Lit1, Lit1Sig, SInputTerms, NInTerms, CurLayer),
    extendAppearingVariables([Lit1], [Lit1Sig], CurLayer, SAppearingVars, NewAppearingVars),
    litsWithAllMatches(SLiterals, NewAppearingVars, NInTerms, SLiteralsSigs, OClauses, OAppearingVars, OInputTerms, OClausesSigs, NLayer, NTLiterals, NTSigs, FInTerms).
    
litsWithAllMatches([Lit1 | SLiterals], SAppearingVars, SInputTerms, [Lit1Sig | SLiteralsSigs], OClauses, OAppearingVars, OInputTerms, OClausesSigs, Layer, NLiterals, NSigs, NInTerms) :-
    (Layer = [CurLayer | NLayer] ; CurLayer = Layer, NLayer = Layer),
    litsWithAllMatches(SLiterals, SAppearingVars, SInputTerms, SLiteralsSigs, OClauses, OAppearingVars, OInputTerms, OClausesSigs, NLayer, NLiterals, NSigs, NInTerms).


hasMatchesInAll(_, _, _, _, [], [], [], []).
hasMatchesInAll(Lit, AppearingTerms, VarsHash, Sig, [CurOClause | OtherOClauses], [CurOAppearingTerms | OtherOAppearingTerms], [CurOVarsHash | OtherOVarsHashes], [CurOSig | OtherOSigs]) :-
    hasMatch(Lit, AppearingTerms, VarsHash, Sig, CurOClause, CurOAppearingTerms, CurOVarsHash, CurOSig),
    hasMatchesInAll(Lit, AppearingTerms, VarsHash, Sig, OtherOClauses, OtherOAppearingTerms, OtherOVarsHashes, OtherOSigs).



%
%
% extendInTerms - add output constants to InTerms
%
%

extendInTerms([], [], IT, IT) :- !.

extendInTerms([LArg | LArgTail], [-SArg | SArgTail], InTerms, NInTerms) :-
    !,
    extendInTerms(LArgTail, SArgTail, InTerms, NInTerms2), 
    add2InTerms(LArg/SArg, NInTerms2, NInTerms), rb_keys(NInTerms, NK).
%    add2InTerms(LArg/SArg, NInTerms2,  NInTerms).

extendInTerms([LArg | LArgTail], [SArg | SArgTail], InTerms, NInTerms) :-
    extendInTerms(LArgTail, SArgTail, InTerms, NInTerms).

extendInTerms(Lit, Sig, InTerms, NInTerms, Layer) :-
    Lit =.. [LitName | LitArgs],
    Sig =.. [_ | SigArgs],
    extendInTerms(LitArgs, SigArgs, InTerms, NInTerms).

%
%
% Extend AppearingVariables
%
%

extendAppearingVariables([], [], Layer, AV, AV) :- !.

extendAppearingVariables([HT|TT], [HS|TS], Layer, CurAV, NewAV) :-
    extendAppearingVariables(TT, TS, Layer, CurAV, TmpAV),
    functor(HT, PredicateName, N),
    LI is N + 1,
    addArgs(HT, HS, PredicateName/Layer, TmpAV, 1, LI, NewAV).

%
%
% addArgs -- adds the output arguments to the AppearingVariables rbtree
% Entries are of the form 
%

addArgs(_, _, _, T, N, N, T) :- !.

addArgs(Lit, Sig, PredName/Layer, InAV, N, LI, NewAV) :-
    arg(N, Sig, -SigVal), !,
    arg(N, Lit, LitVal),
    N1 is N + 1,
    addArgs(Lit, Sig, PredName/Layer, InAV, N1, LI, TempAV),
    add2InTermsWithPath(LitVal/SigVal, PredName/Layer/N, TempAV, NewAV).

% If the argument is either input or constant.
addArgs(Lit, Sig, PredName/Layer, InAV, N, LI, NewAV) :-
    NN is N + 1,
    addArgs(Lit, Sig, PredName/Layer, InAV, NN, LI, NewAV).


% Special case of add args, adds input arguments instead of output
addHeadArgs(_, _, _, In, N, N, In) :- !.

addHeadArgs(Lit, Sig, PredName/Layer, InAV, N, LI, NewAV) :-
    arg(N, Sig, +SigVal), !,
    arg(N, Lit, LitVal),
    N1 is N + 1,
    addHeadArgs(Lit, Sig, PredName/Layer, InAV, N1, LI, TempAV),
    add2InTermsWithPath(LitVal/SigVal, PredName/Layer/N, TempAV, NewAV).

addHeadArgs(Lit, Sig, PredName/Layer, InAV, N, LI, NewAV) :-
    NN is N + 1,
    addHeadArgs(Lit, Sig, PredName/Layer, InAV, NN, LI, NewAV).

%
%
% initAppearingVars
%
%

initAppearingVars(Head, HeadSig, AppVars) :-
    rb_new(TAV),
    functor(Head, PredName, N),
    EN is N + 1,
    addHeadArgs(Head, HeadSig, PredName/0, TAV, 1, EN, AppVars).

initAppearingVarsMulti([], _, []).

initAppearingVarsMulti([Head|Heads], HeadSig, [AppVars | OtherAppVars]) :-
    initAppearingVars(Head, HeadSig, AppVars),
    initAppearingVarsMulti(Heads, HeadSig, OtherAppVars).
%
%
% hasMatch - Check if Lit1 has a matching literal in LitList
%
%

hasMatch(_, _, _, _, [], _, _, _) :- !, fail.

hasMatch(Lit1, Vars1, Vars1Hash, Lit1Sign, [LitListH | LitListT], OVars, OVarsHash, [LitSignListH | LitSignListT]) :-
    schemasMatch(Lit1, Vars1, Vars1Hash, Lit1Sign, LitListH, OVars, OVarsHash, LitSignListH), !.

hasMatch(Lit1, Vars1, Vars1Hash, Lit1Sign, [LitListH | LitListT], OVars, OVarsHash, [LitSignListH | LitSignListT]) :-
    hasMatch(Lit1, Vars1, Vars1Hash, Lit1Sign, LitListT, OVars, OVarsHash, LitSignListT), !.

%
%
% schemasMatch - Check if schemas of Lit1 and Lit2 match.    
%
%

schemasMatch(Lit1, Vars1, Vars1Hash, Lit1Sign, Lit2, Vars2, Vars2Hash, Lit2Sign) :-
    Lit1Sign == Lit2Sign,
    functor(Lit1, _, N),
    LI is N + 1,
    argumentsMatch(Lit1, Vars1, Vars1Hash, Lit1Sign, Lit2, Vars2, Vars2Hash, Lit2Sign, 1, LI).

%
%
% argumentsMatch -- checks if all arguments can be instantiated in the same way.
% What is the point of enumerable constants?
%
%

argumentsMatch(_, _, _, _, _, _, _, _, N, N) :- !.

argumentsMatch(Lit1, Vars1, Vars1Hash, Lit1Sign, Lit2, Vars2, Vars2Hash, Lit2Sign, I, LN) :-
    arg(I, Lit1Sign, +AS1),
    arg(I, Lit2Sign, +AS1), 
    arg(I, Lit1, A1),
    arg(I, Lit2, A2),
    (
    rb_lookup(A1/AS1, OCC1, Vars1),
    rb_lookup(A2/AS1, OCC2, Vars2)
    ;
    rb_lookup(A1/AS1, _/OCC1, Vars1Hash),
    rb_lookup(A2/AS1, _/OCC2, Vars2Hash)
     ),
    rb_intersect_nonempty(OCC1, OCC2),
    NI is I + 1,
    argumentsMatch(Lit1, Vars1, Vars1Hash, Lit1Sign, Lit2, Vars2, Vars2Hash, Lit2Sign, NI, LN).

argumentsMatch(Lit1, Vars1, Vars1Hash, Lit1Sign, Lit2, Vars2, Vars2Hash, Lit2Sign, I, LN) :-
    arg(I, Lit1Sign, #AS1),
    arg(I, Lit2Sign, #AS1),
    setting(par_clp, true), !,
    NI is I + 1,
    argumentsMatch(Lit1, Vars1, Vars1Hash, Lit1Sign, Lit2, Vars2, Vars2Hash, Lit2Sign, NI, LN).

argumentsMatch(Lit1, Vars1, Vars1Hash, Lit1Sign, Lit2, Vars2, Vars2Hash, Lit2Sign, I, LN) :-	
    arg(I, Lit1Sign, #AS1),
    arg(I, Lit2Sign, #AS1),
    ArgNum is LN - 1,
    Lit1 =.. [PredName | _],
    is_clp_predicate(PredName/ArgNum), !,
    NI is I + 1,
    argumentsMatch(Lit1, Vars1, Vars1Hash, Lit1Sign, Lit2, Vars2, Vars2Hash, Lit2Sign, NI, LN). 

argumentsMatch(Lit1, Vars1, Vars1Hash, Lit1Sign, Lit2, Vars2, Vars2Hash, Lit2Sign, I, LN) :-
    arg(I, Lit1Sign, #AS1),
    arg(I, Lit2Sign, #AS1),
    arg(I, Lit1, A1),
    arg(I, Lit2, A1),

    NI is I + 1,
    argumentsMatch(Lit1, Vars1, Vars1Hash, Lit1Sign, Lit2, Vars2, Vars2Hash, Lit2Sign, NI, LN). 

argumentsMatch(Lit1, Vars1, Vars1Hash, Lit1Sign, Lit2, Vars2, Vars2Hash, Lit2Sign, Index, LastIndex) :-
    setting(par_constrain_outputs, true), !,
    arg(Index, Lit1Sign, -AS1), 
    arg(Index, Lit2Sign, -AS1), 
    arg(Index, Lit1, A1),% read vars
    arg(Index, Lit2, A2),
    ( 
	rb_lookup(A1, _, Vars1 ) -> %if existing var -> require match -> armg will request it!
				  !, (
				      rb_lookup(A1/AS1, OCC1, Vars1),
				      rb_lookup(A2/AS1, OCC2, Vars2)
				      ;
				      rb_lookup(A1/AS1, _/OCC1, Vars1Hash),
				      rb_lookup(A2/AS1, _/OCC2, Vars2Hash)
				  ),
				  rb_intersect_nonempty(OCC1,OCC2)
	;
	fail
    ),
    NI is Index + 1,
    argumentsMatch(Lit1, Vars1, Vars1Hash, Lit1Sign, Lit2, Vars2, Vars2Hash, Lit2Sign, NI, LastIndex).

argumentsMatch(Lit1, Vars1, Vars1Hash, Lit1Sign, Lit2, Vars2, Vars2Hash, Lit2Sign, Index, LastIndex) :-
    arg(Index, Lit1Sign, -AS1), 
    arg(Index, Lit2Sign, -AS1),
    NI is Index + 1,
    argumentsMatch(Lit1, Vars1, Vars1Hash, Lit1Sign, Lit2, Vars2, Vars2Hash, Lit2Sign, NI, LastIndex).

%
%
% rb_intersect_nonempty - succsseds if the intersection of two rb_trees is nonempty.
%
%

rb_intersect_nonempty([], []). %for head arguments

rb_intersect_nonempty(RB1, RB2) :-
    rb_keys(RB1, K1),
    rb_keys(RB2, K2),
    member(E, K1),
    memberchk(E, K2).

%
%
% rb_bare - Create a rb-tree with empty lists as leaves
%
%

rb_bare(InTree, OutTree) :-
    rb_keys(InTree, Keys),
    rb_new(NRBT),
    rb_add_bare_nodes(Keys, NRBT, OutTree).

rb_add_bare_nodes([], A, A).

% bare nodes tree for the interms tree (needs to have empty leaves)
rb_add_bare_nodes([H|T], RBT, NRBT) :-
    rb_add_bare_nodes(T, RBT, TRBT),
    rb_insert(TRBT, H, [], NRBT).

%
%
% createBodyStep - createBody without recursion - only returns newly added literals, their signatures etc.
%
%

createBodyStep(CurVarLayer, GenMode, Example, ModeBDecls, UsedPredCalls, InTerms, TermsHash, CurBody, NBody, NUsedPredCalls, NInTerms, NTermsHash, CurBodySignature) :-
  createBodyAtVarDepth(ModeBDecls, GenMode, Example, [], InTerms, UsedPredCalls, InTerms, TermsHash,
                       NBody, NUsedPredCalls, NInTerms, NTermsHash, CurBodySignature),
  updateVarLayer(CurVarLayer, Example, NInTerms, NextVarLayer).

%
%
% add2InTermsWithPath
%
%

add2InTermsWithPath(Key, Value, Tree, NewTree) :-
    rb_lookup(Key, Val, Tree), !,
    rb_insert(Val, Value, [], NSubTree),
    rb_update(Tree, Key, NSubTree, NewTree).

add2InTermsWithPath(Key, Value, Tree, NewTree) :-
    rb_new(NewSubTree),
    rb_insert(NewSubTree, Value, [], SubTree),
    rb_insert(Tree, Key, SubTree, NewTree).


%
%
% add2InTermsWithPath
% 
%

add2HashWithPath(Key, Value, HashTree, Tree, NewTree) :-
    rb_lookup(Key, VarName/Val, Tree), !,
    rb_insert(Val, Value, [], NSubTree),
    rb_update(Tree, Key, NSubTree, NewTree).

add2HashWithPath(Key, Value, HashTree, Tree, NewTree) :-
    rb_lookup(Key, VarName, HashTree),
    rb_new(NewSubTree),
    rb_insert(NewSubTree, Value, [], SubTree),
    rb_insert(Tree, Key, VarName/SubTree, NewTree).


%
%
% stripType - Strips the mode declaration (+, -, #) from type.
%
%

stripType(+Input, Input).
stripType(-Input, Input).
stripType(#Input, Input).

%
%
% termToVar(+Term, +TermsHash, -Var)
%
%

termToVar(Term, TermsHash, Var) :-
    rb_lookup(Term, Var, TermsHash).


%
%
% rb_invert(+Initial_rb, -Inverted_rb)
%
%

rb_invert(RB, IRB) :-
    rb_new(Tmp),
    rb_visit(RB, Pairs),
    rb_invert_aux(Pairs, Tmp, IRB).

rb_invert_aux([], T, T).

rb_invert_aux([Key-Value|Rest], InTree, OutTree) :-
    rb_insert(InTree, Value, Key, TmpTree),
    rb_invert_aux(Rest, TmpTree, OutTree).

%
%
% Map vars to terms 
%
%

vars_to_terms(InTree, InvTermsHash, OutTree) :-
    rb_visit(InTree, InTreeElements),
    rb_new(TTree),
    vars_to_terms_aux(InTreeElements, InvTermsHash, TTree, OutTree).

vars_to_terms_aux([], _, TT, TT).

vars_to_terms_aux([Key/_-Value | Rest], InvTermsHash, InTree, OutTree) :-
    rb_lookup(Key, (NewKey,KeyType), InvTermsHash), !,
    rb_insert(InTree, NewKey/KeyType, Value, TmpTree),
    vars_to_terms_aux(Rest, InvTermsHash, TmpTree, OutTree).

vars_to_terms_aux([Key-Value | Rest], InvTermsHash, InTree, OutTree) :-
    rb_insert(InTree, Key, Value, TmpTree),
    vars_to_terms_aux(Rest, InvTermsHash, TmpTree, OutTree).

initStartBodies([], []).

initStartBodies([E | O], [[] | OO]) :-
    initStartBodies(O, OO).

reverse_all([], []).
reverse_all([L | O], [RL | RO]) :-
    reverse(L, RL),
    reverse_all(O, RO).

rb_invert_all([], []).
rb_invert_all([RB | O], [INVRB | INVO]) :-
    rb_invert(RB, INVRB),
    rb_invert_all(O, INVO).

extendAppearingVariables_all([], [], _, [], []).

extendAppearingVariables_all([CC | OC], [CS | OS], Layer, [CAT | OAT], [NAT | NOAT]) :-
    extendAppearingVariables(CC, CS, Layer, CAT, NAT),
    extendAppearingVariables_all(OC, OS, Layer, OAT, NOAT).

vars_to_terms_all([], [], []).

vars_to_terms_all([CIT | OIT], [CITH | OITH], [CITG | OITG]) :-
    vars_to_terms(CIT, CITH, CITG),
    vars_to_terms_all(OIT, OITH, OITG).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Caching added by Miha Drole
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- dynamic user:satcache/2.
:- dynamic user:parsatcache/8.

cacheExample(Example, ExampleID) :- 
    mode_head(HeadSignature),
    createHead(ExampleID, mode(ground, default), HeadSignature, Head, InputTerms, TermsHash),
    initAppearingVars(Head, HeadSignature, AppearingVars),
    modebDecls(ModeBDecls),
    initialUsedPredCalls(UsedPredCalls),
    initialVarLayer(ExampleID, InputTerms, InVarLayer),
    compute_nwise_bottom_clause_cache(1,InVarLayer, mode(ground,default), [ExampleID], ModeBDecls, [UsedPredCalls], [InputTerms], [TermsHash], [AppearingVars], [[]], Sat, SatSig, [UPC], [IT], [TH], [AV], Layers),
    assert(user:parsatcache(ExampleID, [Head | Sat], [HeadSignature | SatSig], UPC, IT, TH, AV, [0|Layers])).

:- use_module('../examples/examples.pl').
%ffffffuuuuu
partest2 :-
    id2example(806, Z),
    user:parsatcache(Z, A, B, C, D, E, F),
    is_rbtree(F).

generalizeClause(Signature, Clause, Mode, [Head|Body]) :-
    Signature = [HeadSig | BodySig],
    Clause = [ClauseHead | ClauseBody],
    createHead(ClauseHead, Mode, HeadSig, Head, InTerms, Hash),
    generalizeBody(BodySig, ClauseBody, InTerms, Hash, Mode, Body).

generalizeBody([], [], _, _, _, []) :- !.
generalizeBody([LitSig | RestSig], [Lit | Rest], InTerms, Hash, Mode, [GenLit | GenRest]) :-
    generalizeLiteral(Mode, LitSig, Lit, InTerms, Hash, body, GenLit, NewInTerms, NewTermsHash),
    generalizeBody(RestSig, Rest, NewInTerms, NewTermsHash, Mode, GenRest).

numList(_, [], []).
numList(Num, [_|T], [Num | NT]) :-
    numList(Num, T, NT).

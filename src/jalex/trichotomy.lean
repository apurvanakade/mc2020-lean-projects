import tactic

section trichotomy
open tactic expr

meta def tactic.trichotomy (a b : expr) (h : name) : tactic unit :=
do v ← mk_app ``lt_trichotomy [a, b],
rcases none (pexpr.of_expr v)
  [[rcases_patt.one h], [rcases_patt.one h], [rcases_patt.one h]]

namespace tactic.interactive
setup_tactic_parser

open interactive interactive.types expr
meta def trichotomy (a b : parse parser.pexpr) (h : parse with_ident_list): tactic unit :=
do a ← to_expr a, b ← to_expr b,
  nm ← get_unused_name `h,
  let nm := if h = list.nil then nm else h.head,
  tactic.trichotomy a b nm

end tactic.interactive
end trichotomy

example {α : Type*} {c d : α} [linear_order α] 
  (h1 : ¬ c < d) (h2 : ¬ c = d) (h3 : ¬ d < c) : false :=
begin
  trichotomy c d, 
  all_goals { contradiction },
end
import YM.RG12.Strike.Elect
/-! # Literal two-mark diagram evaluation menu (continuum separated Feynman)
   Arity only two. Field horizon and derivative orders arbitrary finite. Predicted coefficient
   includes exact Ward-normalization free terms only through given filtered degree (no way for a
   higher term to be included without supplied degree proof). Provider may use other linear
   group symmetries, or assemble operators in their own precise prescription & simply rewrite
   into `First`. Includes factorials on the integrated local Taylor terms, leaves factorials in any
   field-label Taylor conventions and Wick symmetry/gauge field rules as scalar charges in `Ticket.cost`.
   Inputs are already linearized pure curls; first-order covariantization included among normalization
   terms. No evaluation at generic phases presumed, and no functional claimed on EOM classes without
   expression of the independent formal diagnostics here. Distinguish recipe evaluation from such
   identification including arbitrary lattice amplitude/position-normalized matching.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Strike
open Function Set Filter MeasureTheory Real Finset
open scoped Topology InnerProductSpace ContDiff BigOperators Classical
-- attachment at mark evaluated on a free exterior potential: d curling antisym & displacement signs
-- (−1)^order charged to signed Ticket separately since fixed across all axis/spin sums.
structure Swatch where
  T : Foil
  ink:Poke
  facing:anti T
def Swatch.degree (u:Swatch):ℕ:= u.ink.length+2
abbrev Cards:= List Swatch
def height (c:Cards):ℕ:=(List.map Swatch.degree c).sum
@[simp]lemma weight_cons (a:Swatch)(L:Cards): height (a::L)=a.degree+height L := rfl
@[simp]lemma height_nil : height []=0:=rfl
lemma height_perm {L K:Cards}(h:L.Perm K): height L= height K:=(h.map _).sum_eq

abbrev Crossover:=Swatch×Swatch
structure Brush where
  axis:Axis4 -- vector jet at local finite Taylor correction
  L:Poke
abbrev Gem:=Brush×Swatch
def Brush.degree (b:Brush):=b.L.length+1
def bulk (L:List Gem):ℕ:= (L.map (Brush.degree ∘ Prod.fst)).sum+ height (L.map Prod.snd)
abbrev Gem.use (g:Gem):R→ℂ:=cord g.2.T g.1.L g.2.ink g.1.axis
abbrev Cross.use (k:Crossover):R→ℂ:=ribbon k.1.T k.2.T k.1.ink k.2.ink
variable (P:List Crossover)(V:List Gem)
def curtains(P:List Crossover):= (P.map Cross.use).prod -- orientation reversal optional outside
abbrev uph(P:List Crossover):= height (P.map Prod.fst)+height (P.map Prod.snd)
def pearls(V:List Gem):=(V.map Gem.use).prod
lemma garden_one: Garden (1:R→ℂ) 0 :=⟨fun _ _=>contDiffAt_const,by intro _ _ _ _;simp⟩
lemma strings : Garden (curtains P) (uph P):=by
   induction P with
   | nil=>exact garden_one
   | cons a P he=>
      rw [uph,List.map_cons,List.map_cons,weight_cons,weight_cons]
      unfold curtains; simp only [List.map_cons,List.prod_cons]; convert (ribbon_holds a.1.T a.2.T a.1.ink a.2.ink).times he using 1 <;> first | rfl | skip
      unfold Swatch.degree uph; ring
lemma ringlets : Garden (pearls V) (bulk V):=by
   induction V with
   | nil=>exact garden_one
   | cons a V he=>
      unfold bulk pearls; simp only [List.map_cons,List.sum_cons,List.prod_cons, weight_cons]
      convert (cord_held a.2.T a.1.L a.2.ink a.1.axis).times he using 1 <;> first | rfl | skip
      simp only [Function.comp_apply,Brush.degree,Swatch.degree, bulk]; ring

-- booking specifies each V3 attachment card and the remaining every Wick pair. Both orientations.
-- Coefficients incl color, order, signs at compartment, powers 1/(4π²), diagram combinatorics
-- can be chosen arbitrarily BEFORE probing. So assertion needs no prescribed choice & checks
-- all in same assertion; not defining the Wick pipeline or group colors here.
inductive Ride (A B:Cards) : Type where
  | trip (firstSecond:Bool) (first second third:Swatch)(T:List Crossover)(θ:Farm) -- first-second at active mark, third other
       (h: (if firstSecond then B else A).Perm (first::second::T.map Prod.fst))
       (h': (if firstSecond then A else B).Perm (third::T.map Prod.snd))
  | combined (firstSecond:Bool)(first second third:Swatch)(T:List Crossover)
       (h:(if firstSecond then B else A).Perm (first::second::third::T.map Prod.fst))(h':(if firstSecond then A else B).Perm (T.map Prod.snd))
  | term (actingSecond:Bool)(P:List Gem) -- finite-term local jet/gauge-covariantized field. open every stroke
       (h:(P.map Prod.snd).Perm (if actingSecond then A else B))(he:(P.map (Brush.degree ∘ Prod.fst)).sum ≤ height (if actingSecond then B else A))
structure Receipt (A B:Cards) where
   leg: Ride A B
   cost:ℂ
def activeDir (b:Bool)(f:R→ℂ):=fun x:R=> if b then f (-x) else f x
variable (χ:R→ℂ)(hχ:Base χ){A B:Cards}
def Ride.view (y:Ride A B) : R→ℂ:=match y with
 | .trip b U V W T θ _ _=> activeDir b (curtains T * gala U.T V.T W.T U.ink V.ink W.ink χ θ)
 | .combined b U V W T _ _ => activeDir b ((fun x:R=> curtains T x*(tank χ U.T V.T W.T U.ink V.ink W.ink)))
 | .term b P _ _=> activeDir b (pearls P)
def simpleReport (Y:List (Receipt A B)) : R→ℂ:=(Y.map (fun y=>fun x:R=>y.cost*y.leg.view χ x)).sum
include hχ
omit hχ in
private lemma dir {k}{F:R→ℂ}{b:Bool}(he:First k F):First k (activeDir b F):=by cases b with
                                                                        | true=>exact First.turn he
                                                                        | false=>exact he
lemma Ride.buy (p:Ride A B): First (height A + height B) (Ride.view χ p) := by
   cases p with
   | trip b a c d T θ h h'=>
     unfold Ride.view; apply dir -- linter included unused
     have H := First.wire (strings T) (First.core χ a.T c.T d.T a.ink c.ink d.ink θ a.facing c.facing d.facing hχ)
     have hp:=height_perm h;have he:=height_perm h'; convert H using 1; cases b <;> simp only [Bool.false_eq_true,if_false,if_true,weight_cons] at hp he <;> rw [hp,he] <;> unfold uph profile Swatch.degree <;> ring
   | combined b a c d T h h'=>
     unfold Ride.view; apply dir
     change First _ ((curtains T) * fun _=>tank χ a.T c.T d.T a.ink c.ink d.ink)
     have hp:=height_perm h;have he:=height_perm h'; convert First.wire (strings T) (First.dam χ a.T c.T d.T a.ink c.ink d.ink hχ) using 1
     cases b <;> simp only [Bool.false_eq_true,if_false,if_true,weight_cons] at hp he <;> rw [hp,he] <;> unfold uph profile Swatch.degree <;> ring
   | term b P h he=>
     unfold Ride.view;apply dir
     apply First.classV _ (ringlets P)
     have hf:=height_perm h; cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true] at he hf <;> unfold bulk <;> omega
-- applies to ANY polarization & Wick combinatorial choices and gauge/correction, frame first derivative.
-- Match to any regulated A array by pinning the needed exact coefficients separately!
theorem offers (r:List (Receipt A B)): First (height A+height B) (simpleReport χ r) := by
   induction r with
   | nil=> exact First.nil _
   | cons p r he=> exact First.join (First.weight (Ride.buy χ hχ _) p.cost) he
end YM.RG12.Strike

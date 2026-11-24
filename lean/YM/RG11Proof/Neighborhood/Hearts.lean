import YM.RG11Proof.Neighborhood.Feelers

/-!
# Separated OPE characterized by power/log reproduction

On `conf`, all compact smooth internal geometries and external singleton
and multi positions from `Lens`, on same independently tested smooth
correlations + shifts consistency. Output C(v) through H in tower F H.
Test coefficient f linear/polarized labels by array v. No growing-log
schedule assumptions for IDENTIFICATION here. Error definition uses
EventRate, coefficients *ordinary*, arbitrary ζ>0 possibly order & horizon
dependent. Can consume a next-horizon remainder giving 1. ζ exact in
transported result. Excludes unit contacts; unit at leading grade zero kept
included. This file assumes Wilson side (e.g. RG10) exact power-log normalized
OPE with this reproduction rule (and **that** covariance on the chosen scale
for all positive t, distributions or functions); translation to a different
normalization/separation/geometries in either scheme needs a proof. Derives
existence uniquely for the MS side & transformation, no assuming it. Not
claiming actual Reader is this object, need further bridges.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Neighborhood
open scoped Classical BigOperators ContDiff Topology
open Set Function Filter MeasureTheory Labels Maxwell
open PowerSeries YM.RG11.Grove YM.RG11.Stress YM.RG11.Jets YM.RG11.Nodes YM.RG11.Fields YM.RG11.Scale YM.RG11.Window
variable {G:Gauge}{F:Frames G}

abbrev Blocks (F:Frames G)(n i H:ℕ):=Grove.Cabinet (sheaf F n i) (lab F H)
abbrev wlog (F:Frames G){n i H:ℕ}(v:sheaf F n i)(j:lab F H):ℝ:= ((worth v:ℕ):ℝ)-grade F H j

/-- OPE C for FIXED center/input shape(s), all exterior positions. Include
all remaining horizons, separations positive may approach (estimate constants
can depend fixed x,c,y,m,input ext and H-order). Need smooth-continuum
representation on both A & B NORMALIZED schemes, including free piece.
Any different CS/contact/angular convention that changes position powers
or Ward field-map needs explicit adapter. -/
structure Snug (A:ShapeReport G F){n i H:ℕ}(u:Design n) (c:E4)(N:ℕ)(δ:ℝ)(C:Blocks F n i H) :Prop where
    decay : 0 < δ
    -- all positive internal rescalings; exact. if your system only specifies
    -- asymptotic OPE terms near zero, identify polynomials instead & extend.
    sharp : Affords (fun v j=>season (wlog F v j)) N C
    def_ray (m e:ℕ)(y:Tail m)(h:y.c=c):
       EventRate N H δ (fun v : sheaf F n i=>worth v) (fun s=>frontRow A i e u y s) (backRow A H e y) C

-- transported candidate. Positive power precision does not depend on arbitrary
-- arbitrary support interpolants. p intended X t in M g for A=X.

def crown {n i H}(p:PowerSeries ℝ)(X:∀i, Window.SquareAt F i)(C:Blocks F n i H):Blocks F n i H :=
   reassign (Jets.deposit p) (castNet (X i) n) (fieldInv (X H)) C
namespace Snug
 theorem walks {A B:ShapeReport G F}{T: Window.AxisData A}{M:Window.AxisData B}{p:PowerSeries ℝ}{X:∀ i,Window.SquareAt F i}(h:Window.Direction A T B M p X)
    {n i H:ℕ}{u:Design n}{c:E4}{N:ℕ}{δ:ℝ}{C:Blocks F n i H}(hS:Snug A u c N δ C):
    Snug B u c N δ (crown p X C):=by
   have hx (i:ℕ):nearId (plank (X i)):=by
      have Ht:nearId (X i):=(h.legal i).field.baseline
      ext j l
      change coeff 0 (Jets.deposit (X i j l))= _; rw [deposited,←piece_apply (A:=X i),Ht, Matrix.one_apply,Matrix.one_apply]; split_ifs <;> simp
   have hD (i:ℕ):graded (grade F i) (plank (X i)):=plank_grade _ (fun e=>h.graded_X i e)
   have hI(n i:ℕ):graded (fun i=>worth i) (castNet (X i) n):=cluster_grade (s:=plank (X i)) (v:=grade F i) (fun e=> hD i e)
   have hb:Anchored (Jets.deposit p):=deposit_base p (h.legal i).ruler.base
   have hz: fieldInv (X H)*plank (X H)=1:=squareInv_mul (hx H)
   have hu:graded (grade F H) (fieldInv (X H)):=by
      intro a b e
      -- handle Fin decidable
      convert! graded.Law_inv (w:=grade F H) (A:=plank (X H)) (fun e=> hD H e) (by convert! hx H) e using 1
   refine ⟨hS.decay,?_, fun m d y he=>?_⟩
   · exact graded_season (R:=fieldInv (X H)) (L:=castNet (X i) n) (X:=C) (N:=N) hb (fun v=>hI n i v) (fun v=>hu v) hS.sharp
   exact translate (Jets.deposit p) (castNet (X i) n) (plank (X H)) (Matrix.transpose (castNet (X d) m)) (N:=N) (W:=fieldInv (X H)) (C:=C) (A:=frontRow B i d u y) (B:=backRow B H d y) (fun h=>hI n i h) (by convert! hz) hb
      (fun s=> Matrices.linked A B h i d (u.taps (Real.exp (-s)) y) N) (rear_linked h H d _ N) (hS.def_ray m d y he)

 theorem singular {A:ShapeReport G F}{n i H}{u:Design n}{c:E4}{N:ℕ}{δ:ℝ}{C X:Blocks F n i H}(h:Snug A u c N δ C)(hX:Snug A u c N δ X):
    ∀ s, MatThrough N (C s) (X s):=by
   have hc : c≠c-basis 0:=by intro ht; apply (show basis 0≠(0:E4) from fun he=>by simpa using congrArg norm he); apply neg_injective; apply add_left_cancel (a:=c); simpa [sub_eq_add_neg] using ht.symm
   let y:=oppositePoint c _ hc
   obtain ⟨W,hW⟩:= light A H c _ hc
   let I(s:ℝ): Rect (sheaf F n i) (lab F H) (PowerSeries ℂ) := (frontRow A i H u y s).submatrix id (fun j (_:Fin 1)=>j)
   have he (x:Blocks F n i H)(he:Snug A u c N δ x):EventRate N H δ (fun t=>worth t) I (shore A H y) x:=by
      intro j a k hv; exact he.def_ray 1 H y rfl j (fun _:Fin 1=>a) k hv
   apply free_unique W (w:=grade F H) (fun i=> (tower F H).heights i) (by convert! hW) h.decay (he C h) (he X hX) h.sharp hX.sharp

 -- lower δ and order weakenings; permits exponents on X unknown.
 theorem allowance {A:ShapeReport G F}{n i H:ℕ}{u:Design n}{c:E4}{N:ℕ}{δ:ℝ}{C:Blocks F n i H}(h:Snug A u c N δ C){ε}(he:0<ε)(hz:ε ≤ δ){K}(hk:K≤N):Snug A u c K ε C:=
    ⟨he,fun a b k h'=> h.sharp a b k (h'.trans hk),fun m d y hyv a b k ho=> individually (by linarith) (h.def_ray m d y hyv a b k (ho.trans hk))⟩

 theorem vision {A:ShapeReport G F}{n i H}{u:Design n}{c:E4}{N:ℕ}{δ δ':ℝ}{C X:Blocks F n i H}(h:Snug A u c N δ C)(hX:Snug A u c N δ' X):
     ∀ s, MatThrough N (C s) (X s):=singular (h.allowance (lt_min h.decay hX.decay) (min_le_left ..) le_rfl) (hX.allowance (lt_min h.decay hX.decay) (min_le_right ..) le_rfl)
end Snug

end YM.RG11.Neighborhood

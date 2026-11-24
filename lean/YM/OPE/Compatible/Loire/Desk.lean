import YM.OPE.Compatible.Loire.Wick
/-!
# Auxiliary color regulator. Finite shapes at arbitrary charge
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Shrew
open Function MeasureTheory Set Topology Metric Filter Lattice Laurent Wilson Exterior Cascade PertExtension Series Score Next.Foundations Matrix
open Next.Free Frequency Bloch MSbar.Tree MSbar.Tree.Resolvent Terp Stubble Weir
open GaussianScore Libra WithLp RG Precision Votive Glass Radial Flume.Script Flock StageLight Balsam Nestle
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {n:Side}{G:Gauge}{C:KernelChoices}{U:Gloam}{r:ℕ}
lemma rawCov (p:Crew U)(x:Cover)(H:∀ i,Even (U.M i).val):Cleared U (fun i=>mildX [] (p.val i+wrap _ x)):=by
    by_cases hp:p.val 0=0
    · have hx(i):p.val i=0:=by induction i with | zero=>exact hp|succ i ih=>rw [p.property i,ih,← Ratio.root_embed,map_zero]
      simp_rw [hx,zero_add]; obtain ⟨c,h⟩:= fromCore (inhabitC U x [] (Eventually.of_forall H)); rw [show (fun i=>_)= (fun i=> seam [] (U.M i) x)+(fun _=> hull [] x) from funext fun i=>Eq.symm (sub_add_cancel ..)]; exact h.full.fuse Cleared.always
    obtain ⟨c,h⟩:= (shores [] p.property hp).lo.sell x; exact h.full
structure Yarn (U:Gloam)(G:Gauge) where
    nest : Crew U
    charge : G.ColorIndex
    a : Axis
    u : Cover
variable (H:∀ i,Even (U.M i).val)
abbrev slips (a:Yarn U G)(i:ℕ): Module.Dual ℝ (Keys G (Limb (H i))) := Tags (H i) a.charge a.a (a.nest.val i+wrap _ a.u)
lemma bis (hr:4 ≤ r)(a b:Yarn U G):Cleared U (fun i=>(boost (H i) (Train.top r) hr C).wick (slips H a i) (slips H b i)):=by
   let L(p:Yarn U G)(i:ℕ):=p.nest.val i+wrap _ p.u; let Q:=ShellRow C (Train.top r); change Cleared _ (fun i=> boostJet _ _ _ _ _ _ (L a i,_) (L b i,_)); simp_rw [pages]; split
   next hh=>
      have he(j:Kv): Cleared U (fun i:ℕ=> Terp.letter Q (addressR (L a i,a.a)) (L b i,b.a) j):=by
          let k:= fun i:ℕ=> decks j (b.nest.val i); let v:Crew U:=⟨(fun i=>k i-a.nest.val i), fdroon (orbitB0 U b.nest j H) a.nest.property⟩; have ht(i): decks j (L b i)=k i+wrap _ ((axisK j).act b.u):=by unfold k L decks affine; rw [Signed.act_add, wrap_signed];abel
          let T(i:ℕ):= decks j (L b i)+wrap _ (spotK j b.a); have hh(i:ℕ): (ferry j (L b i,b.a))=(T i,b.a):= ferry_at _ _ _
          let A(i:ℕ):=lineC Q _ (addressR (T i,b.a)) (addressR (L a i,a.a)); let I:Cover:= (axisK j).act b.u+spotK j b.a-a.u
          have hi(i):A i=if b.a=a.a then mildX [] (v.val i+wrap _ I) else 0:=by
               change lineC (ShellRow C (Train.top r)) (U.M i) (T i,coord b.a) (L a i,coord a.a)= _; rw [strip_field hr, if_congr (Exterior.coord_iff ..) (by rfl) (by rfl)] -- likely
               congr 2; unfold T I; rw [ht,map_sub,map_add]; change k i+_+_-(a.nest.val i+_)=_ ; change _= k i-a.nest.val i+_; abel
          have hA:Cleared U A:=by
            rw [funext hi];split
            · exact rawCov _ I H -- maybe split∀
            exact cleared_zero _
          simp_rw [Terp.letter,hh]; split
          · exact hA.glu (- ContinuousLinearMap.id ℝ ℝ)
          exact hA
      convert! Cleared.tally (U:=U) Finset.univ (fun j i=> Terp.letter Q (addressR (L a i,a.a)) (L b i,b.a) j) (fun j _=>he j) using 2 with i
   exact cleared_zero _
end YM.OPE.Shrew

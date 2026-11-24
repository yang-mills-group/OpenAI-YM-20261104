import YM.OPE.Compatible.Frog.Tonga
/-!
# phase lifts
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Drift
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Paver Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module
variable {n c f:Side}{I J:Type}{G:Gauge}{r i j d m l k:ℕ}
variable {τ:Phase→ℕ}
local notation "T!"=> Tower (Shade G) d τ
lemma spirits {p:Script (Shade G) k}{a:ℝ}(h:soot r p a)(H:r≥2*l)(x: Page (Shade G) l): Summable fun i=>p i * coff (ships i) l x:=(((paySpray G 0 r k l (by omega)).choose_spec.2 p a h).2.collectible (fun i=>Page.payer 0 i) x).of_norm -- ambiguity
lemma growAdd (x:Phase){p q:Script (Shade G) r}{a b:ℝ}(h:soot m p a)(hq: soot m q b)(hm:2*(r+2)≤ m): glide (Grid.lance (p+q)) x=glide (Grid.lance p) x +glide (Grid.lance q) x:=by
     have he(i:Phase): timbre ships (p+q) (r+i.val)= timbre ships p (r+i.val)+timbre ships q (r+i.val):=by
          ext1 j; have hz:2*(r+i.val)≤m:=by have h:=i.isLt; omega
          unfold timbre; simp only [Pi.add_apply,add_mul]; exact (spirits h hz j).tsum_add (spirits hq hz j)
     have hp(i:Phase): Grid.lance (p+q) i=Grid.lance p i+Grid.lance q i:=by unfold Grid.lance Shell.throw; rw [he i]; exact map_add (LinearMap.single ℝ (fun i=> Script (Shade G) i) _) ..
     ext1 i; unfold glide; rw [Pi.add_apply]; split
     next hx=>simp
     next hx=> exact hp _
lemma growS (x:Phase)(p:Script (Shade G) r)(c:ℝ): glide (Grid.lance (c • p)) x=c • glide (Grid.lance p) x:=by
     have he(i:Phase): Grid.lance (c • p) i=c • Grid.lance p i:=by
          have hv(k:ℕ): timbre ships (c • p) k=c• timbre ships p k:=by ext1 i; unfold timbre;simp only [Pi.smul_apply,smul_eq_mul,mul_assoc,tsum_mul_left]
          unfold Grid.lance; rw [hv]; exact map_smul (LinearMap.single ℝ (fun i=> Script (Shade G) i) _) ..
     ext1 i; unfold glide; rw [Pi.smul_apply]; split; next hx=>simp
     next hx=> exact he _
lemma burst (h:Aware d τ)(x:Phase): ∀ i: Fin (d+x.val+1), ∀ t:Phase,∃ a:ℝ,0 ≤ a∧∀ p:Script (Shade G) i.val,∀ b:ℝ,p.sorted→ p.abides→ soot (τ x) p b → Volume (glide (Grid.lance p) x t) (d+t.val) (if t=x then τ t else τ t+1) (a*b):=by
     intro i t; have ht:2*(i.val+2) ≤ τ x:=by have h:=h.credit x; have hp:=x.isLt; omega
     have hv:i.val≤d+x.val:= Nat.le_of_lt_succ i.isLt
     by_cases he:t=x
     · subst t; refine ⟨1,zero_le_one,fun p b hp hh hP=>?_⟩; have h₀:0≤b:=Sack.coins hP; rw [if_pos rfl,glide_me,one_mul]
       rw [show Grid.lance p 0= Shell.throw (timbre ships p i.val) from rfl,frameO hh hp hP (he:=by omega)]
       refine ⟨fun i hi=> hubbub (by omega),fun j=>?_⟩; by_cases h:j=i.val; subst j; erw [show Shell.throw p i.val=p from Pi.single_eq_same ..]; exact hP; rw [hubbub h]; exact Sack.zero h₀ _
     by_cases hx:t<x; · refine ⟨0,le_rfl,fun p b hp hh hP=>?_⟩; rw [glide_nil _ hx, zero_mul]; exact ⟨fun _ _=>rfl,fun i=> Sack.zero le_rfl _⟩
     have hg:x.val≤t.val:=Fin.le_iff_val_le_val.mp (le_of_not_gt hx); have hM:= h.margin x t (lt_of_le_of_ne (le_of_not_gt hx) (Ne.symm he)); have hL:= x.isLt; obtain ⟨a,ha,H⟩:= Grid.crib G _ _ (τ x) (τ t+1) hv (by omega); refine ⟨a,ha,fun p b h₁ h₂ hP=>?_⟩
     rw [if_neg he]; unfold glide; rw [if_neg hx]; exact (H p b hP ⟨t.val-x.val,(by have h:= t.isLt; omega)⟩).raise _ (show d+x.val+(t.val-x.val)≤d+t.val from by omega) le_rfl
-- roster as impulse
abbrev baby (x:Phase)(p:Seat (d+x.val) (τ x) (Shade G)):Muse G:= ∑ i:Fin (d+x.val+1), glide (Grid.lance (lilies (τ x) (d+x.val) _ p i.val)) x
lemma lancing (p:Script (Shade G) k)(x:Phase):Rainbow (glide (Grid.lance p) x):=by
     intro i j; by_cases he:i<x
     · rw [glide_nil _ he]; exact fun _=> rfl
     unfold glide; rw [if_neg he]; let q:Phase:=⟨i.val-x.val,by have h:=i.isLt;omega⟩; change sorted (Shell.throw (timbre ships p (k+q.val)) j); by_cases h:j=k+q.val
     · subst j; rw [show Shell.throw _ _=_ from Pi.single_eq_same (k+q.val) (timbre ships p (k+q.val))]; exact timbreT _ _ _
     rw [hubbub h]; exact fun _=>rfl
end YM.OPE.Drift

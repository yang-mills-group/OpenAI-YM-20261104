import YM.OPE.Compatible.Spades.Color
/-!
# Expected magnitudes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Spells
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{E X F:Type}{n:Side}(o:Site n){b i k r m:ℕ}{K:KernelChoices}
open Finset
lemma cupV (C:KernelChoices)(v:Train i)(h:4 ≤ i)(x y:FreeResolvent.Slot G n 1): ‖Silt.chamber (Vessel C v G n h) (flats G n).toContinuousLinearMap x y‖ ≤ (rentV G v h C n).fare:=by
       rw [(Hport C v G n h).choose_spec.1]; obtain ⟨⟨p,z⟩,rfl⟩:= (station G n).surjective x; obtain ⟨⟨q,w⟩,rfl⟩:=(station G n).surjective y; let T:=rentV G v h C n; let V:=CapeV C G v n; have hh:= dripped G v h C p (0:Cover) (lift (q-p):Cover) z w; rw [_root_.map_zero,add_zero,wrap_lift,add_sub_cancel] at hh; exact (congrArg norm hh).trans_le (T.lease z w _) -- implicit
lemma drams (C:KernelChoices)(v:Train i)(h:4 ≤ i)(b:ℕ)(x y:Fpaper G b): ‖Silt.chamber (Vessel C v G n h) (VScan G b o ∘L (flats G n).toContinuousLinearMap) x y‖ ≤ (rentV G v h C n).fare:=by
       let f(i:Fpaper G b):=station G n (o+wrap n i.1.val.1,(i.1.val.2,i.2)); exact cupV C v h (f x) (f y)
lemma scoopμ (b:ℕ)(n:Side)(o:Site n)(h:2*(b+1)<n.val):sizeQ b ≤1+(b+b+1:ℝ)^4*4:=by
       have he: Injective (fun i:TilesB b=> Spindle.reads i o):=by
             have hh(i:TilesB b): register h (Spindle.reads i o)=i:= by
                  apply Subtype.ext; refine Prod.ext ?_ rfl; change lift ((wrap n i.val.1+o)-o)=i.val.1; rw [add_sub_cancel_right,borne h i.val.1 i.property.1]
             exact LeftInverse.injective (g:=register h) hh
       have hv:=Fintype.card_le_of_injective _ he; have hp: (Fintype.card (TilesB b)) ≤ (b+b+1)^4*4:=hv.trans (by simpa only [Dim,Fintype.card_coe] using broad o b); apply add_le_add_right; exact_mod_cast hp
variable {I J:Type}[Fintype I][Fintype J]
open Cascade.Paver
lemma paletteS [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](A:Law E)(S:E→L[ℝ] PAD I)(T:PAD I→L[ℝ] PAD J)(v C:ℝ)(x y:J)(hp:‖T‖≤v)(hv:0≤ C)(h:∀ i j, ‖Silt.chamber A S i j‖≤C):
       ‖Silt.chamber A (T ∘L S) x y‖ ≤ C*(Fintype.card I)^2*v^2:=by
            let a(j:J):=coQ T j; let D(j):= crewZ (a j); let V:=chamber A S; let K:=Fintype.card I; have hh:0≤v:=(norm_nonneg _).trans hp; have hm(i j):‖D i j‖≤ v:=by
                 have hx:= norm_le_pi_norm (T (Pi.single j 1)) i; exact hx.trans ((T.le_opNorm _).trans (by rw [Pi.norm_single, norm_one, mul_one]; exact hp))
            rw [show Silt.chamber _ _ x y=A.wick ((a x).comp S.toLinearMap) ((a y).comp S.toLinearMap) from rfl, Salvet]; change ‖∑ i:I,D x i* (∑ j:I,V i j *D y j)‖ ≤ _; refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun _:I=> v*((K:ℝ)*(C*v))) (fun i _=>?_)).trans_eq ?_)
            · rw [norm_mul]; refine mul_le_mul (hm ..) ?_ (norm_nonneg _) hh; exact (norm_sum_le ..).trans (le_trans (sum_le_sum (g:=fun _=> C*v) fun j _=>by rw[norm_mul]; exact mul_le_mul (h _ _) (hm _ _) (norm_nonneg _) hv) (by simp [K]))
            rw [Finset.sum_const,card_univ,nsmul_eq_mul]; unfold K; ring
abbrev cookV (G:Gauge)(v:Train i)(K:KernelChoices)(h:4 ≤ i)(n:Side)(b:ℕ):= (rentV G v h K n).fare * (Fintype.card (Fpaper G (4*b)))^2*((strideSize G).choose * ((1+8*(b:ℝ))*(strideSize G).choose))^2
lemma avenue (v:Train i)(K:KernelChoices)(h:4 ≤ i)(b:ℕ)(x y:Fpaper G b): ‖Silt.chamber (Vessel K v G n h) (Cane G b o) x y‖ ≤ cookV G v K h n b:=by
       let T:=VScan G (4*b) o∘L (flats G n).toContinuousLinearMap; let p:= (strideG G b).toContinuousLinearMap; let q:= (strideG G (4*b)).symm.toContinuousLinearMap; let P:= p ∘L (socket b ∘L q); let C:=(strideSize G).choose; let X(j:ℕ):=(strideSize G).choose_spec.2 j; -- Z
       let f:=socket b (G:=G); have hz:(Cane G b o)=P ∘L T:=by
            ext1 i; let Y:= scanf G (4*b) o ((flats G n) i); change p (f Y)= p (f (q (strideG G (4*b) Y))); rw [show q _= _ from (strideG G (4*b)).symm_apply_apply Y]
       let G₁:= (strideSize G).choose_spec.2; rw [hz]; refine paletteS _ T P _ _ x y ((ContinuousLinearMap.opNorm_comp_le ..).trans ?_) (rentV G v h K n).positive (drams o K v h (4*b)); refine mul_le_mul (G₁ b|>.1) ((ContinuousLinearMap.opNorm_comp_le ..).trans (mul_le_mul (RootNorm b) (G₁ _|>.2) (norm_nonneg q) (by positivity))) (norm_nonneg _) (zero_le_one.trans ((strideSize G).choose_spec.1))
end YM.OPE.Spells

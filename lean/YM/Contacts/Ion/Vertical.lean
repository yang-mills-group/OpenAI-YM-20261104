import YM.Contacts.Sequent.Mild
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.RingTheory.PowerSeries.Substitution
import YM.UVNext.PRICED_KERNELS.Read
namespace YM.Contacts.Lyre
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Resetter Shuttle.Tide
open Procession Procession.Welcome Procession.Catch Procession.Sun Procession.Lotus Procession.Hinges Procession.Xenon
open Shuttle.Pigment Prairie Harrier Sequent
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{b c d g:ℝ}{X Y A B ι κ α β: Type}{m:Side}{n k i r l j M D:ℕ}{ζ σ:ℝ≥0}
open UVNext PricedKernels Next.Free Lattice Tree FreeResolvent
set_option autoImplicit false
section geom
variable {f L:Side}(g:Ratio m f)(x y:Site m)
local notation "ℓ"=> g.count.val
lemma total_scaled : separation (g.embed x) (g.embed y)=ℓ*separation x y:= by
    refine le_antisymm (scaled_root ..) ?_; unfold separation pdist; rw [←g.root_embed, ←g.root_embed,← map_sub,g.root_embed,g.lift_embed]; let Z:= lift (x-y); let F:= Finset.univ (α:=Axis); let S(t:Cover):= F.sup (fun i=> (t i).natAbs); let h: F.Nonempty:= univ_nonempty; obtain ⟨i,hi,he⟩:=exists_mem_eq_sup F h (fun i=>(Z i).natAbs); change ℓ*S Z ≤ S (ℓ • Z); unfold S; rw [he]; refine le_trans (b:=((ℓ • Z:Cover) i).natAbs) (?_) (Finset.le_sup (f:=fun j=> ((ℓ • Z:Cover) j).natAbs) hi); simp [Pi.smul_apply,Int.natAbs_mul]
lemma across (x y:Site m): separation (-x) (-y)=separation x y:= by unfold separation; rw [show -x- -y= -(x-y) from by abel,pdist_neg]
abbrev aging (ζ:ℝ≥0)(x:Site m):= gained ζ x (-x)
lemma aging_one (x:Site m):1≤aging ζ x:= Real.one_le_exp (by positivity)
lemma split_pre (u:Site f)(hx:2*σ≤ ζ): aging σ x ≤ aging σ u * gained ((ζ:ℝ)/(g.count.val:ℝ)) u (g.embed x):= by
    let n:=g.count; let l:ℝ:=n.val; let a:=g.embed x; let A:ℝ:= separation x (-x); let B:ℝ:= separation u (-u); let C:ℝ:= separation u a; have hc:0 ≤ C:= Nat.cast_nonneg _; have he:a=g.root x:= rfl -- ratio def?
    have hp: separation a (-a) ≤ (separation u a) + (separation u (-u)+ separation u a):= by
       conv_rhs=>arg 1; rw [separation_comm]
       exact (separation_triangle a u (-a)).trans (Nat.add_le_add_left ((separation_triangle u (-u) (-a)).trans (Nat.add_le_add_left (le_of_eq (across ..)) _)) _) -- conv semicolon bad
    have hA:n.val*separation x (-x)=separation a (-a):= by
        rw [←total_scaled (m:=m) g]; have ha:g.embed (-x)=-a:=(g.root_embed _).symm.trans (map_neg g.root x)
        rw [ha]
    have hB:l*A≤ C+(B+C):= by unfold l A C B; exact_mod_cast hA.trans_le hp
    have hv:(σ:ℝ)*2≤ζ:= by exact_mod_cast ((mul_comm σ 2).trans_le hx)
    have ht:l≥1:=Nat.one_le_cast.mpr n.property; have hl:0<l:=lt_of_lt_of_le zero_lt_one ht; change Real.exp ((σ:ℝ)*A) ≤Real.exp ((σ:ℝ)*B)*Real.exp ((ζ:ℝ)/l*C); rw [← Real.exp_add]; apply Real.exp_monotone; apply (mul_le_mul_iff_of_pos_right hl).1; field_simp; have hq:0≤ (σ:ℝ)*B:= mul_nonneg (NNReal.coe_nonneg _) (Nat.cast_nonneg _); nlinarith only [mul_le_mul_of_nonneg_left hB (NNReal.coe_nonneg σ),mul_le_mul_of_nonneg_right ht hq,mul_le_mul_of_nonneg_right hv hc]
end geom
-- propagated absolute kernel in singular norm uses this weighted estimate. no contract assertion.
section lease
variable (e:Parcel G)(p:Parcel.Word)(s:Parcel.Step)(n:Side)
def holiday (x:ℝ) := trFee e.J x e.tax
abbrev output:= Spark.atr G (e.traveler s n) (installed (e.traveler s n).ratio (e.gas p s))
lemma tensor_price {i:ℕ}{f m:Side}(A:Matrix (Body i f) (Body r m) ℝ)(g:Ratio m f) {t a:ℝ}(h:Annuity (PricedKernels.site f _) (PricedKernels.parent g _) A t a): Annuity (PricedKernels.site f _) (PricedKernels.parent g _) (tensor G A) t a:= by
    rintro ⟨x,b,d⟩; refine le_trans (b:= ∑ y, gained t x (g.embed y.1)* |A (x,b) y|) ?_ (h (x,b)); simp only [FreeResolvent.tensor, Matrix.of_apply, UVNext.PricedKernels.site, UVNext.PricedKernels.parent, Fintype.sum_prod_type,apply_ite abs, abs_zero, mul_ite, mul_zero]; simp -- adjust
local notation "Γ"=> (e.reach:ℝ)
lemma treasury : Annuity (PricedKernels.site (n*s.L) _) (PricedKernels.parent (e.traveler s n).ratio _) (Lyre.output e p s n) (Γ/(s.L.val:ℝ)) (holiday e Γ):= by
    let Y:=e.gas p s; let S:=e.traveler s n; let T:= S.ratio; let P:= installed T Y; have hg:0<Γ:= NNReal.coe_pos.mpr e.reach_pos; have he : Y.strip Γ (e.tax/(s.L.val:ℝ)):= by let h:=e.rod p s [] (by simp); change Y.strip Γ (e.tax/(s.L.val:ℝ)^(1+0:ℕ)) at h; simpa only [add_zero,pow_one] using h
    apply tensor_price; let h:= Annuity.paid_cross (g:=T) he hg.le; let C:= PricedKernels.stackFee Γ e.tax (TypeFace 1); apply extract_price S Γ hg.le _ P C (stackFee_nonneg _ _ e.tax_pos.le); apply h.cut le_rfl; refine le_of_eq ?_; unfold C PricedKernels.stackFee; change Real.exp _ * ( (Fintype.card (TypeFace 1):ℝ)*(_/(s.L.val:ℝ))) = _ / (s.L.val:ℝ); ring
end lease
end
end YM.Contacts.Lyre

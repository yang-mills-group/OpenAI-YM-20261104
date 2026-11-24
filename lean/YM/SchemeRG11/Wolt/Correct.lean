import YM.SchemeRG11.Wolt.Wain
/-! Canonical prechange targets; admissible real field columns.
 Need only SIGNED-symmetrized profile for position. -/
noncomputable section
set_option autoImplicit false
namespace YM.SchemeRG11.Wolt
open Function Filter Asymptotics Topology MeasureTheory Metric
open Flock Lattice Pert Align Full Maxwell Haze Pile Catch World Atoll Tree Acorn Outlook Banner
open Labels Long MvPolynomial Air North
open scoped Classical Pointwise
variable {G:Gauge}{n m:ℕ}{T: Align.Itinerary}{c:ℕ→ Sky G n→ℝ}{R r:ℝ}{B:Window} {F:Falls G}{p:pLabel G}
lemma harvestY (h:IsWeightedHomogeneous generation p n)(hp:B.rOut<r)(hv:r<R)(hB:Blue T R F)(hc:Tone c)(he:Twin T R n F (shapeV T c)): Finishes (fun i=> T.gap i^(-(n:ℤ))*(aeval (F i) (crestF p T B r i)- spry T c n (crestF p T B r i) i)):=by
 have hh:=avails (lt_trans (B.rIn_pos.trans B.rIn_lt_rOut) (hp.trans hv)) hc ((Atoll.land G).heat (castFirst 1 p)) hB he
 have hk:= (Finishes.of (Air.weaken_less (p:=-(n:ℤ)) hh (by omega))).add (ward_walk B h hp hv hB hc he)
 apply hk.same; apply Eventually.of_forall; intro i; dsimp only; unfold crestF; rw [frameB,map_add]
 simp only [spry,map_add,map_sum]; rw [Finset.sum_sub_distrib]; ring
lemma high_ev (h:IsWeightedHomogeneous generation p n)(hp:B.rOut<r)(hc:Tone c):Finishes (fun i=> (T.gap i)^(-(n:ℤ))*aeval (rooms T c i) (margin p T B r n n i)):=by
 let M (i:ℕ):= margin p T B r n n i
 let F:Set (Size G n):={v|rankW inkAge v ≤ n}
 haveI : Finite F:= width_finite _ n (fun a=> Nat.le_add_left 1 _)
 letI : Fintype F := Fintype.ofFinite _
 let s:= Finset.univ.image (Subtype.val (p:=fun (v:Size G n)=>v∈F))
 have hs(i): (M i).support ⊆ s:= by
    have hh:M i∈ Ladder n n:= Submodule.sub_mem _ ledge ledge
    intro k w; exact Finset.mem_image.mpr ⟨⟨k,(MvPolynomial.mem_restrictSupport_iff ℝ).mp hh w⟩,Finset.mem_univ _,rfl⟩
 change Finishes (fun i=> _*aeval _ (M i)); simp_rw [tablature (M _) (rooms T c) _ s (hs _),Finset.mul_sum,stairs_scale]; apply Finishes.sum _ -- unify function
 intro i hi; refine ((Banner.spike (T:=T) i p h hp).mul (toneS i hc)).same (Eventually.of_forall ?_); intro j
 change T.gap j^(bill i-n)*coeff _ _*_=_; unfold M; rw [sub_eq_add_neg,zpow_add₀ (T.positive _).ne']; ring
lemma composed {f g:ℕ→ℝ}(h:f=O[atTop] Air.latch T ((n:ℤ)+1))(hp:Tendsto (fun i=>T.gap i*g i) atTop (𝓝 0)): Tendsto (fun i=>T.gap i^(-(n:ℤ))*g i*f i) atTop (𝓝 0):=by
 let p(i):=T.gap i^( - ((n:ℤ)+1)) * f i
 obtain ⟨C,hC,H⟩:= hatch_iff.mp h; have he:∀ᶠ i in atTop,|p i| ≤ C:=by
    filter_upwards [H] with i h; unfold p; rw [abs_mul,abs_of_pos (zpow_pos (T.positive _) _)]; apply le_trans (mul_le_mul_of_nonneg_left h (zpow_pos (T.positive i) _).le); rw [mul_left_comm (T.gap _ ^ _), ←zpow_add₀ (T.positive _).ne',neg_add_cancel,zpow_zero,mul_one]
 apply tendsto_zero_iff_norm_tendsto_zero.mpr
 refine squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) ?_ (show Tendsto (fun i=> ‖T.gap i*g i‖*C) atTop (𝓝 0) by simpa using hp.norm.mul_const C)
 filter_upwards [he] with i hi; rw [show (T.gap i)^(-(n:ℤ))*g i *f i= T.gap i*g i*p i from ?_,norm_mul]; exact mul_le_mul_of_nonneg_left hi (norm_nonneg _)
 change _ =_*(_ * _); rw [← mul_assoc]; congr 1; rw [mul_right_comm]; congr 1; nth_rw 2 [← zpow_one (T.gap i)] 
 rw [← zpow_add₀ (T.positive _).ne',show (1:ℤ)+-(n+1:ℤ) = -(n:ℤ) by omega]
variable (G) in
lemma output (F:Labels.Frames G)(T: Itinerary)(B:Window)(h:IsWeightedHomogeneous generation p n)(v:Neutral p)(hp:B.rOut<r) : ∃ m,∃ q:Fin m→Tab F n,∃ M:ℕ→ Fin m→ℝ,(∀ a,Tendsto (fun i=>T.gap i*M i a) atTop (𝓝 0))∧∀ (F':Falls G)(R:ℝ), r<R→ Blue T R F'→ Finishes (fun i=> T.gap i ^(-(n:ℤ))*aeval (F' i) (crestF p T B r i-∑ a:Fin m,M i a • stemZero 1 (q a).p)):=by
 obtain ⟨m,I,P,H⟩:= platen n n F; let U i:=spume p v (gateY T r i) (cove T B i) n n; let M i:= P (U i)
 have he(a:Fin m):Tendsto (fun i=> T.gap i*M i a) atTop (𝓝 0):=lim_s _ _ h hp (LinearMap.proj a ∘ₗ P)
 refine ⟨m,I,M,he,fun F' R hv hb=>?_⟩; have hR:0<R:=B.rIn_pos.trans (B.rIn_lt_rOut.trans (hp.trans hv))
 obtain ⟨c,t,l⟩:= cloudNet n hb hR; let q(i):= crestF p T B r i
 have he1 (i): spry T c n (q i) i -∑a:Fin m, M i a * spry T c n (stemZero 1 (I a).p) i= aeval (rooms T c i) (margin p T B r n n i):=by
   unfold spry margin; rw [map_sub]; apply congrArg (_ - ·); change _= aeval _ (U i).val
   rw [H (U i),map_sum]; apply Finset.sum_congr rfl; intro j _;rw [map_smul];rfl
 have ht(a:Fin m):= composed (avails hR t (stemZero 1 (I a).p) hb l) (he a)
 apply (((harvestY h hp hv hb t l).add (high_ev h hp t)).sub (Finishes.sum Finset.univ _ (fun a _=> Finishes.of (ht a)))).same
 filter_upwards with i
 rw [_root_.map_sub,← he1,map_sum]; simp only [smul_eq_mul, map_smul]
 simp_rw [mul_sub,Finset.sum_sub_distrib,mul_assoc, ← Finset.mul_sum]; unfold q; abel

end YM.SchemeRG11.Wolt

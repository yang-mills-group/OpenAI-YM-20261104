import YM.XSpace.Raise
/-!
# Core relief test — all open Wick symbols on registered test legs

Hypothesis `Scored` to discharge separately, not papering sign arrays (later with
position context). For chosen inputs and at scaling filters $S$. K subtraction still
here before full regulator bookings.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Chapter
open Function Set Filter Lows Scale Mu Uptown Normalize Maxwell Maxwell.Free MvPolynomial Next.Rank.Normal Contraction Finsupp Future Drama Asymptotics Prelude Bracket Furlough Lattice
open scoped Topology BigOperators ContDiff
variable {G:Gauge}{d k:ℕ}
abbrev World (G:Gauge):= Trace.Contact G
variable {ι:Type}{L:Filter ι} {A:ι→ World G}{a:ι→ℝ}{r:ι→ℕ}(B:ι→Hat G d) (K:Studio L a r A) (hb:Likely L B)(h:Tendsto a L (𝓝 0))(he:∀ᶠ i in L,0<a i)(H:∀ᶠ i in L,orchestra d (a i) (B i)=gather d (A i))
def Fares (a:ℝ)(X: Trace.Contact G)(B:Hat G d):Module.Dual ℂ (Stamp G):= (Chart2.pit X).toLinearMap-(view (orchestra _ a B)).toLinearMap ∘ₗ trunc coin d ∘ₗ (overture d).toLinearMap
lemma fares (a:ℝ)(X:World G)(B:Hat G d)(p:Stamp G) : Fares a X B p=Chart2.pit X p-LTop p a B:=rfl
private def Bound (A:ι→World G)(B:ι→Hat G d)(a:ι→ℝ)(p:Stamp G)(L:Filter ι):Prop := (fun i=> tick a i (d+1)* Fares (a i) (A i) (B i) p)=O[L](fun _=>(1:ℝ))
private lemma monoKnown (v: Trace.UnitIndex G→₀ℕ)(c:ℂ): Book G (Finsupp.weight (fun _: Trace.UnitIndex G=> (1:ℕ)) v) (fun _=>monomial v c):=by
  classical apply Extra.FD.per_factor v; change Book G _ (fun _=> C c); rw [map_zero]; convert Book.scale Book.unit c using 1; funext x; change _=c • (1: Stamp G); rw [← C_mul',mul_one]
  intro u i h; rw [monomial_add_single,map_add,weight_single,pow_one,one_smul,← wall_entry i]; exact h.mul (Book.left (freeLeg i))
include hb K h he H
private lemma const_bound {p:Stamp G}(hn:Book G k (fun _=>p)): Bound A B a p L:=by
  have hi (i): Fares (a i) (A i) (B i) p= Remainder (fun _=>p) A B a i 0:= rfl
  obtain ⟨s,C,hC,H⟩:=outer 1 B K he le_rfl hb H _ hn; apply IsBigO.of_bound C; filter_upwards [he,H,K.lives.eventually_ge_atTop s,h.eventually (ge_mem_nhds zero_lt_one)] with i hi' hp hr hx
  specialize hp (0:Cover) (by simpa using hr) (by simpa [area] using hx); rw [hi,tick,norm_one,mul_one,norm_mul,norm_pow,norm_inv,Complex.norm_real,Real.norm_of_nonneg hi'.le]; apply (mul_le_mul_of_nonneg_left hp (pow_nonneg (inv_pos.mpr hi').le _)).trans_eq; simp only [Sail.reach_zero,area,Nat.cast_zero,add_zero,Sail.carry,inv_one,one_pow,mul_one]; rw [inv_pow]; field_simp
private theorem has_bounds (p:Stamp G): Bound A B a p L:=by induction p using MvPolynomial.induction_on' with
  | monomial a c=> exact const_bound B K hb h he H (monoKnown ..)
  | add p q i j=> unfold Bound; simp_rw [_root_.map_add,mul_add]; exact IsBigO.add i j
private lemma por {V:Type*}[AddCommGroup V][Module ℂ V] [FiniteDimensional ℂ V](f:V→ₗ[ℂ] Stamp G)(p:ι→V)(hh:By ℂ L (fun i=>(a i:ℂ) • p i) 0):
    Tendsto (fun i=> tick a i d* Fares (a i) (A i) (B i) (f (p i))) L (𝓝 0) :=by
  classical let Z:=Module.finBasis ℂ V; let g (i:ι):Module.Dual ℂ V:=tick a i (d+1) • (Fares (a i) (A i) (B i) ∘ₗ f); let u i:=(a i:ℂ) • p i
  have he₀(x:V): (fun i=> g i x)=O[L](fun _=>(1:ℝ)):=has_bounds B K hb h he H _
  have hp(j):Tendsto (fun i=> Z.coord j (u i) • g i (Z j)) L (𝓝 0):=by
    have ht: (fun i=> g i (Z j))=O[L] (fun _=>(1:ℂ)):= by obtain ⟨C,H⟩:= isBigO_iff.mp (he₀ (Z j)); apply IsBigO.of_bound C; simpa using H
    have hp:= hh (Z.coord j); rw [map_zero] at hp; apply (IsBigO.trans_tendsto ((isBigO_refl (fun i=>Z.coord j (u i)) L).mul ht)); simpa only [u,mul_one] using hp
  have heY:= tendsto_finsetSum Finset.univ fun i _=> hp i; simp only [Finset.sum_const_zero] at heY; refine heY.congr' ?_
  filter_upwards [he] with i hi; change ∑ j:Fin (Module.finrank ℂ V),_=_; rw [show tick a i d*_= g i (u i) from ?_]; swap; · unfold g u; simp only [LinearMap.smul_apply,LinearMap.comp_apply,map_smul,smul_eq_mul,tick]; rw [pow_succ]; have hp:(a i:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hi.ne'; field_simp
  conv_rhs=>arg 2; rw [← Z.sum_repr (u i)]; skip
  rw [map_sum]
  exact Finset.sum_congr rfl (fun j _=> (map_smul (g i) _ _).symm)
variable (c: Shade.Cut)[L.IsCountablyGenerated](W:Initialize G)(p:On.Grade G d)

def compCost (a:ℝ) := (a:ℂ)⁻¹ ^d • compensate W c d a p
def safety (L:Filter ι)(a:ι→ℝ)(c:Shade.Cut)(A:ι→ World G): Prop := Sees L a (fun _=>0) A ∧ ∀ x:E4,‖x‖≤ c.rOut→ x≠0 → Sees L a (fun i=> Further.FreeCovariance.KP.mark (a i) x) A
include H he hb
-- Moment lemma at positive-order vertex, along ALL such frontages k mesh families
lemma solid (hp:Shade.Safety c r L a) (hz:safety L a c A): Likely L fun i=>Chart2.pit (A i) (compCost (d:=d) c W p (a i)) :=by
  set σ:=W.surveys d; let f i:= Fares (a i) (A i) (B i); let F i:=tick a i d; let P i:= compensate W c d (a i) p; have hu(i:ι): Chart2.pit (A i) (compCost (d:=d) c W p (a i))= F i*f i (P i)+ F i*LTop (P i) (a i) (B i):= by unfold f P; rw [fares,← mul_add,sub_add_cancel,compCost,map_smul];rfl
  simp_rw [hu]; apply Likely.add _ (wires W c h he p hb); change Likely L fun i=> F i*f i (screen1 W c d (a i) p - _); simp_rw [map_sub,mul_sub]; refine Likely.sub ?_ (?_); swap
  · exact ⟨_,por B K hb h he H (screenplay W d) (fun i=> repair W c d (a i) p) (greeting W c h he p)⟩
  change Likely L fun i=> F i*f i (fuse σ p c (a i)); simp_rw [drama,map_sub,_root_.map_sum,mul_sub,Finset.mul_sum]; apply Likely.sub
  · let L':= LinearMap.toSpanSingleton ℂ (Stamp G) (mark1 σ p); have h₀ : By ℂ L (fun i=> (a i:ℂ) • (1:ℂ)) 0:=by intro g; simp_rw [map_smul, map_zero]; simpa only [zero_smul,Complex.ofReal_zero] using! (Complex.continuous_ofReal.continuousAt.tendsto.comp h).smul_const (g 1)
    have ht:=por B K hb h he H L' (fun _=>1) h₀; simp [L'] at ht; exact ⟨_,ht⟩
  apply Likely.sum _ _ ; intro j _; set P₀:=spirit σ p j; have hv:= (Shade.sum_lesson c h he B K P₀ (vetting σ p j) hp hb H hz.1 hz.2).2; refine hv.congr (Eventually.of_forall fun i=>?_)
  dsimp only; unfold Remainder; rw [tsum_eq_sum (s:=(Shade.outfit c (a i)).support), Shade.quick_sum, _root_.map_sum,Finset.mul_sum]; swap
  · intro x hx; rw [← Shade.outfit_eq,Finsupp.notMem_support_iff.mp hx,mul_zero,zero_mul]
  exact Finset.sum_congr rfl fun x hx=>by rw [map_smul]; change F i*_ * (f i (P₀ x))=F i*(_ * _); ring
end YM.XSpace.Chapter

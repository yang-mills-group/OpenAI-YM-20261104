import YM.RegulatorIR.Pupil.Post
import YM.RegulatorIR.Gain.OnAir

/-!
# W1 expense over noncompact poles
One array (Cutoff), ℓ¹ fields. No limits commuted in regulator sense. Evaluating
the finite coefficient is by compactly supported sections of fields on COVER.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Skein
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries Gradient Pupil Cluster
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries
variable {G:Gauge}{I J Y:Type}{p r e i k:ℕ} {A:BEdge G}{σ:Cover→G.Color}
-- detect ℓ1. cost-norm using ENN absolute.
def Roots (A:BEdge G): Prop:= (∑' x, ‖A x‖ₑ)≠⊤
def Spire (A: Cover→ G.Color): Prop:= (∑' x, ‖A x‖ₑ)≠⊤
lemma footwise (g:Edge Cover→ℝ≥0∞)(h:(∑' x,g x)≠⊤): (∑' x:Foot G,g x.1)≠⊤:=by rw [ENNReal.tsum_prod']; simp_rw [tsum_fintype,sum_const];simp only [card_univ,nsmul_eq_mul,ENNReal.tsum_mul_left];exact ENNReal.mul_ne_top (by finiteness) h
lemma iterable {u:Cover→ℝ≥0∞}(h:(∑' x,u x)≠⊤): (∑' x: Edge Cover,u x.1)≠⊤∧(∑'x:Edge Cover,u (x.1+step x.2))≠⊤:=by
 have hp:(∑' x:Edge Cover,u x.1)≠⊤:=by
    change (∑' x:Cover×Axis,u x.1)≠⊤;rw [ENNReal.tsum_prod']; simp_rw [tsum_fintype,sum_const]; simp only [card_univ,nsmul_eq_mul,ENNReal.tsum_mul_left]; exact ENNReal.mul_ne_top (by finiteness) h
 refine ⟨hp,?_⟩
 let e:Equiv.Perm (Edge Cover):= { toFun:=fun p=>(p.1-step p.2,p.2),invFun:=fun p=>(p.1+step p.2,p.2),left_inv:= fun p=>by simp, right_inv:=fun p=>by simp }
 rw [← e.tsum_eq]; change (∑' x: Edge Cover,u (x.1-step x.2 + step x.2))≠⊤;simpa
lemma sheaf {c:I→ℝ≥0∞}(hc:(∑' x,c x)≠⊤)(p:ℕ): (∑' x,c x^(p+1))≠⊤:=by
 apply ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top (n:=p) hc) hc);rw [← ENNReal.tsum_mul_left];apply ENNReal.tsum_le_tsum;intro i;rw [pow_succ]; apply mul_le_mul_left (pow_le_pow_left' (ENNReal.le_tsum i) _)

-- summable per-leg through varying z for $vow*$
def Quips (A:BEdge G)(σ:Cover→G.Color) (z:Side):= vow (shadowU (sachet A z) (bonnet σ z))
def Tallied (u:Side→I→PowerSeries ℝ)(i:ℕ):Prop:=∃ v:I→ℝ≥0∞,(∑' x,v x)≠⊤∧ ∀ z x,‖coeff i (u z x)‖ₑ≤v x
lemma lore (h:Roots A)(hm:Spire σ):∀ i,Tallied (Quips A σ) i:=by
 let f(x: Edge Cover):= ‖A x‖ₑ+ (‖σ x.1‖ₑ+‖σ (x.1+step x.2)‖ₑ)
 have Hs:(∑' x,f x)≠⊤:=by
                             obtain ⟨hr,ht⟩:=iterable (u:=fun x=>‖σ x‖ₑ) hm -- fix
                             unfold f; simp_rw [ENNReal.tsum_add]; exact ENNReal.add_ne_top.mpr ⟨h, ENNReal.add_ne_top.mpr ⟨hr,ht⟩⟩
 have hu(i z): ‖violet (sachet A z) (bonnet σ z) i‖ₑ ≤ f i:=by
    let v:= bonnet σ z;let q:=sachet A z
    have hx(y): ‖v y‖ₑ≤ ‖σ y‖ₑ:=by unfold v bonnet; split <;> first| rfl|simp
    have hh(y):‖q y‖ₑ≤ ‖A y‖ₑ:=by unfold q sachet;split <;> first| rfl|simp
    have hh': ‖violet (sachet A z) (bonnet σ z) i‖ₑ=max ‖q i‖ₑ (max ‖v i.1‖ₑ ‖v (i.1+step i.2)‖ₑ):=by rw [← golden,←ofReal_norm,violet,Prod.norm_def];simp_rw [ENNReal.ofReal_max, ofReal_norm];rfl
    rw [hh']; unfold f; apply max_le ((hh ..).trans le_self_add); exact le_trans (max_le ((hx ..).trans le_self_add) ((hx (i.1+step i.2)).trans le_add_self)) le_add_self
 intro i; obtain ⟨c,hc,H⟩:= route_bound (G:=G) i; refine ⟨fun p=>c*(f p.1)^(i+1),?_,fun z x=>le_trans (H (violet (sachet A z) (bonnet σ z) x.1) _) (mul_le_mul_right (pow_le_pow_left' (hu ..) _) _)⟩
 rw [ENNReal.tsum_mul_left]; exact ENNReal.mul_ne_top hc (sheaf (footwise f Hs) _)
lemma mora (h:Roots A) i:Tallied (fun z=>vow (fun _=>hue (sachet A z))) i:=by
 let f(x:Foot G):= ‖A x.1‖ₑ; refine ⟨f,footwise _ h,fun z x=>?_⟩
 change ‖coeff i (tale (fun _=> (sachet A z x.1) x.2))‖ₑ≤ _
 rw [tale_const,PowerSeries.coeff_C]; split; next hi=>
     unfold sachet; split; apply le_trans (b:=‖A x.1‖ₑ); rw [← ofReal_norm,←ofReal_norm];apply ENNReal.ofReal_le_ofReal (PiLp.norm_apply_le ..)
     rfl
     simp
 simp
lemma Tallied.multiply {U:Side→I→PowerSeries ℝ}(H:∀ i≤p,Tallied U i)(r:ℕ):∀ i≤p,Tallied (fun z x=>pip (U z) x (r:=r)) i :=by
 induction r with
 | zero=> intro i hi; refine ⟨fun _=>‖coeff i (1:ℝ⟦X⟧)‖ₑ,?_,fun z x=>by simp [pip]⟩; simp
 | succ r ih=>
    intro i hi; let J:=antidiagonal i
    choose! f hf hF using H;choose! g hg hG using ih
    let G (j:ℕ×ℕ) (x:Tuple I (r+1)):= f j.1 (x 0) * g j.2 (Fin.tail x)
    refine ⟨fun p=> ∑ j∈ J,G j p,?_,?_⟩
    · rw [Summable.tsum_finsetSum (f:=G) (fun _ _=> ENNReal.summable)]; apply ENNReal.sum_ne_top.mpr; intro j hj; have hv:= mem_antidiagonal.mp hj; rw [← (Tuple.glueEquiv I r).tsum_eq];change (∑' i:I× Tuple I r,f j.1 i.1*g j.2 i.2)≠⊤; rw [ENNReal.tsum_prod']; simp_rw [ENNReal.tsum_mul_left,ENNReal.tsum_mul_right]; exact ENNReal.mul_ne_top (hf _ (by omega)) (hg _ (by omega))
    intro z x; dsimp only; rw [show pip (U z) x= U z (x 0)*pip (U z) (Fin.tail x) from Fin.prod_univ_succ _,coeff_mul];apply (enorm_sum_le ..).trans; apply sum_le_sum; intro j hj;have ht:=mem_antidiagonal.mp hj; exact (enorm_mul ..).trans_le (mul_le_mul' (hF _ (by omega) _ _) (hG j.2 (by omega) z _))
lemma Quips.limitR {V:Orders I}{C:Side→I→PowerSeries ℝ}{u:I→ PowerSeries ℝ}(hq:∀ i≤p,Tallied C i)(H:Learn u C atTop p) (h:∀ i ≤ p,∀ r, Limits (V i r)) (hp:i≤p) (m:ℕ): Tendsto (fun z=>rhymeR (C z) V m i) atTop (𝓝 (rhymeR u V m i)):=by
 unfold rhymeR; apply tendsto_finsetSum;intro j hj;apply tendsto_finsetSum;intro r _
 let a:=j.1;let b:=j.2; have hx:= Finset.mem_antidiagonal.mp hj; let t:= V a r
 obtain ⟨c,hc,h'⟩:= h j.1 (by omega) r
 obtain ⟨f,hf,hF⟩:=Tallied.multiply hq r j.2 (by omega); let g(z:Side) (x):= t x * coeff b (pip (C z) x)
 have he(z x): ‖g z x‖ ≤ (c*f x).toReal:=by
    apply (ENNReal.ofReal_le_iff_le_toReal (ENNReal.mul_ne_top hc (ne_top_of_le_ne_top hf (ENNReal.le_tsum x)))).mp;rw [ofReal_norm];exact (enorm_mul ..).trans_le (mul_le_mul' (h' x) (hF ..))
 have hM:Tendsto (fun z=>∑' x,g z x) atTop (𝓝 (rhyme u t b)):=tendsto_tsum_of_dominated_convergence (ENNReal.summable_toReal (show (∑' x,c*f x)≠⊤ from by rw [ENNReal.tsum_mul_left]; exact ENNReal.mul_ne_top hc hf)) (fun x=>(H.pip r j.2 (by omega) x).const_mul (t x)) (Eventually.of_forall he)
 exact hM

lemma agreesW (i) : ∀ᶠ z:Side in atTop,Quips A σ z i=vow (shadowU A σ) i:=by
 filter_upwards [included i.1.1,included (i.1.1+ step i.1.2)] with z hz ht;unfold Quips vow shadowU violet; simp_rw [sachet,bonnet,if_pos hz,if_pos ht]
lemma chalkW (x): ∀ᶠ z:Side in atTop,vow (fun _=> hue (sachet A z)) x=vow (fun _=> hue A) x:=by
 filter_upwards [rises_v A x.1] with z hz;unfold vow hue;simp_rw [hz]

variable {T:Orders (Foot G)}(H:W1 T p)
include H
lemma knowsL (A:BEdge G)(σ:Cover→G.Color)(h:Roots A)(ht:Spire σ)(hh:∀ i≤p,∀ r,Limits (T i r))(he:e≤p): rhymeR (vow (shadowU A σ)) T 2 e = rhymeR (vow (fun _=>hue A)) T 2 e:= by
 have hp: Learn (vow (shadowU A σ)) (Quips A σ) atTop p:=fun i _ x=> tendsto_const_nhds.congr' ((agreesW ..).mono (fun v hv=> Eq.symm (congr_arg _ hv)))
 have hl:= Quips.limitR (C:=fun z=>vow (fun _=>hue (sachet A z))) (u:=vow (fun _=> hue A)) (fun i _=>mora h i) (fun i _ x=> tendsto_const_nhds.congr' ((chalkW x).mono (fun v hv=> Eq.symm (congr_arg _ hv)))) hh he 2
 refine tendsto_nhds_unique (Quips.limitR (fun i _=> lore h ht i) hp hh he 2) ?_; exact hl.congr (fun z=> (H.grade _ _ (sachet_s ..) (bonnet_v ..) e he).symm)
end YM.RegulatorIR.Skein

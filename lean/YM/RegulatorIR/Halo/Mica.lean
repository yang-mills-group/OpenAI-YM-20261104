import YM.RegulatorIR.Halo.Heart

/-!
# Ward at all finite t paths for quotient and *restricted periodic bulk*

*Derived* for bulk even if only its own deck symmetry given. Proof uses bare
archive theorem on much larger arenas. Doesn't require Ward convergence premise
before using loop budget; here lengths fixed per original array. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Halo
open Function Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Step Matrix StopB Ward Uniform Finset Sight
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff
variable {G:Gauge} {i W₀ s a p k w e m:ℕ}{W:Type}{M:W→ℕ}{n:Page M→Side}{S:Heir n G}
variable (H:Reel S)(T:S.Accounts)
variable {L:Meter W} (B: S.Supplies T L p k)(C:Aug.Amenities S L p k) (ht:14≤k)
variable (hp: H.Follows T)(hr:Common H)
variable (w:W) (i:ℕ)(h:i<M w)
local notation "v" => ticketE w i h
local notation "E" => eternal H w
local notation "g" => grove H w hr
local notation "P" => tele H T w

include C B hp ht hr
lemma defectC {t:i ≤ M w}{x:ℝ→ Horizon G (n (Page.mk w i t))}
 (hh: Layer.Sym (S.maps ⟨w,i,t⟩) (S.maps ⟨w,i,t⟩) (H.stem ⟨w,i,t⟩))(hB:Billed (H.stem ⟨w,i,t⟩))
 (hx:ContDiffAt ℝ ∞ x 0) {j:ℕ} (h':j ≤ p) : Carry Aug.light 1 fun z=> let p:=Aug.sheet w i t z; let m:= Sight.slab z; let t₀:= signed m x; ‖coeff j (money ((g).stance p) ((P).orb p) t₀)-counts m* coeff j (money (H.stance (Page.mk w i t)) (haloT T (Page.mk w i t)) x)‖ₑ:=by
 let q(z:Side):= Aug.sheet w i t z; let f z:= signed (Sight.slab z) x; let u(z:Side):=(P).orb (q z);let t₀ z:=haloT P (q z);let D(z:Side):=u z-t₀ z
 have ht' :Full (X:=fun z=>Book G (big w n (q z))) (fun z=>vow (peel (f z))) j:=by intro i hi; obtain ⟨c,h,H⟩:=noted x hx j i hi;exact ⟨c,h,fun z t=> H (Sight.slab z) t⟩
 have hf(z:Side) : coeff j (money ((g).stance (q z)) (u z) (f z))- counts (Sight.slab z)*coeff j (money (H.stance (Page.mk w i t)) (haloT T (Page.mk w i t)) x) = rhymeR (vow (peel (f z))) (D z) 2 j:=by
    rw [← canonC H T w i x hx hr B hh hB z h']; change _ - coeff j (money ((g).stance (q z)) (t₀ z) (f z))= _; rw [← rhyme_tube,← map_sub];apply congr_arg;unfold money;change _-_ = reel (u z-t₀ z) _ _; simp_rw [reel,reel_split]; rw [map_sub]; abel
 change Carry _ _ fun z=> ‖coeff j (money ((g).stance (q z)) (u z) (f z)) - counts (Sight.slab z)*coeff j _‖ₑ; simp_rw [hf]
 refine songs_many (Y:=fun z=>Book G (big w n (q z))) ?_ ht'
 intro r hc a
 by_cases eh: a=0
 · subst a; have h(z:Side):D z r 0=0:=by
      have hp :∀ p:Page (extent M w),(P).orb p r 0=0:=by
         apply Page.proves
         · intro x; change singer H T w x r 0=0; ext1 u; rw [singer,Deck.deckSum,dif_neg (by omega)];rfl
         intro p _;rw [← (P).step_o p]; unfold GridStep.common; split; rfl;contradiction
      unfold D; rw [Pi.sub_apply,Pi.sub_apply, show u z r 0=0 from hp _]; have he: t₀ z r 0=0:=by ext1 u; unfold t₀ haloT; rw [Deck.deckSum,dif_neg (by omega)];rfl
      rw [he,sub_self]
   simp_rw [h,quota_zero];exact Carry.zeroQ _
 let f₀(z:Side):= D z r a
 have H' : Claim Aug.light ((Aug.lpost H w i t).pear 1) 1 f₀:= Aug.horizons H T (Aug.Amenities.enough C (show k≥Aug.glaze 1 from ht)) (Aug.T_enough T B ht) hp hr w i t _ (hc.trans h') _ (by omega)
 exact Carry.mono H' fun z=> quota_mono (D z r a) fun b=>Premium.width_unit ..

variable {x y: ℝ→ Horizon G (n (ticketE w i h))}
lemma defect (hx:ContDiffAt ℝ ∞ x 0) {j:ℕ} (h':j ≤ p) : Carry Aug.light 1 fun z=> let p:=Aug.sheet w i h.le z; let m:= Sight.slab z; let t:= signed m x; ‖coeff j (money ((g).stance p) ((P).orb p) t)-counts m* coeff j (money (H.stance v) (haloT T v) x)‖ₑ:= defectC H T B C ht hp hr w i (H.moduli ⟨w,i,h⟩).sym.1 (H.moduli ⟨w,i,h⟩).rows.1 hx h'
omit C B hp ht hr in
lemma flash (x:ℝ) (h:Carry Aug.light 1 fun z=>‖counts (Sight.slab z)*x‖ₑ): x=0:=by
 obtain ⟨f,⟨c,p,hc,H⟩,hp⟩:=h
 have he (u:Side):‖counts (Sight.slab u)*x‖≤ c.toReal:= by
    apply (ENNReal.ofReal_le_iff_le_toReal hc).mp; rw [ofReal_norm]; exact (hp u).trans ((show f u * 1≤_ from mul_le_mul_left (H u) _).trans_eq (by change c*1^p*1= _; simp))
 by_contra! hx; have hx':0<‖x‖:= norm_pos_iff.mpr hx; obtain ⟨n,hn⟩:= exists_nat_gt (c.toReal/‖x‖);have hn':0<n:= Nat.cast_pos.mp (lt_of_le_of_lt (div_nonneg ENNReal.toReal_nonneg hx'.le) hn)
 let u:Side:=⟨n,hn'⟩;specialize he u
 have hl:(n:ℝ)≤counts (Sight.slab u):=by unfold counts; have hz:(n:ℝ)≤(Sight.slab u).val := (Nat.cast_le.mpr (le_mul_of_one_le_left (show 0 ≤ n from Nat.zero_le _) (show 1 ≤ (4:Side).val by decide))); have hx:1≤(n:ℝ):=by exact_mod_cast hn'
                                         exact hz.trans (le_self_pow₀ (hx.trans hz) (by decide))
 have hs:0≤counts (Sight.slab u):= (by positivity : 0 ≤ (n:ℝ))|>.trans hl
 rw [norm_mul, Real.norm_of_nonneg hs] at he;exact ((not_lt.mpr ((mul_le_mul_of_nonneg_right hl hx'.le).trans he)) ((div_lt_iff₀ hx').mp hn))

variable (Z:T.Report m){U:W→Portrait G}(hU:∀ i,BasisT m s (U i) (Z.main (Page.opening M i)))
variable (hx:ContDiffAt ℝ ∞ x 0)(hy:ContDiffAt ℝ ∞ y 0)(hd:Ward.reel_prop x y)
include hU hx hy hd
-- exact ϑ-restricted perVac
lemma mica : Squares p (money (H.stance v) (haloT T v) x) (money (H.stance v) (haloT T v) y):=by
 intro j hj; apply sub_eq_zero.mp;apply flash
 have hy'(z:Side) : let F:=Aug.sheet w i h.le z;let Q:=(P).orb F; money ((g).stance F) Q (signed (Sight.slab z) x)= money ((g).stance F) Q (signed (Sight.slab z) y):=by
    intro F Q; obtain ⟨A⟩:= glowing H T Z hp U hU w hr F
    exact Ward.RangeR.norms A (wave _ hx) (wave _ hy) (waveV _ (H.even v) hd)
 apply Carry.mono (Carry.add (defect H T B C ht hp hr w i (show i<M w from by assumption) hx hj) (defect H T B C ht hp hr w i (show i<M w from by assumption) hy hj)); intro z
 let m:= Sight.slab z; let K:= counts m; let L:= coeff j (money (H.stance v) (haloT T v) x); -- inspect
 let t:= coeff j (money (H.stance v) (haloT T v) y)
 let Q:= (g).stance (Aug.sheet w i (by omega) z)
 let Q':=(P).orb (Aug.sheet w i (by omega) z)
 let a:= money Q Q' (signed m x);let b:=money Q Q' (signed m y)
 change ‖K*(L-t)‖ₑ≤‖coeff j a-K*L‖ₑ+ ‖coeff j b-K*t‖ₑ
 rw [show a=b from hy' z, show K*(L-t)= -(coeff j b-K* L)+(coeff j b-K*t) by ring, ← enorm_neg (coeff j b-K*L)] -- rew wrong occ
 exact enorm_add_le ..
-- archive orbit and both wallets
lemma corsage : Squares p (reel (T.change v) 2 x) (reel (T.change v) 2 y):=by
 have ht':= hinted H T Z hp U hU
 obtain ⟨g'⟩:= Coverage.craved T Z H.docket _ ht' v
 let s:=T.orb v
 have hx': money (H.stance v) s x= money (H.stance v) s y:= Ward.RangeR.norms g' hx hy hd
 have hp':= mica H T B C ht hp hr w i h Z hU hx hy hd
 have he u: reel (T.change v) 2 u= money (H.stance v) s u-money (H.stance v) (haloT T v) u:=by
    rw [money,money, show T.change v=s-haloT T v from rfl]; unfold reel;rw [reel_split,map_sub];abel
 rw [he x,he y]; exact Squares.sub (fun i hi=>by rw [hx']) hp'
end YM.RegulatorIR.Halo

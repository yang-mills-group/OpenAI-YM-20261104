import YM.Contacts.Procession.Comet
/-!
# Post & pre costs on this same path

Keep polynomial cost in e.Z. Used on any join horizon (pre-calibration of frames).
-/
noncomputable section
namespace YM.Contacts.Procession.Port
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Sun Xenon Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Welcome Resetter Shuttle.Tide
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
open Tree FreeResolvent Draw PhysicalNext.RankCovariance Catch Hinges Lotus Welcome.Theater
open Barrage Barrage.Slope Barrage.Reserve Barrage.Reserve.Oasis Odor Odor.Winding Odor.Winding.Sales
set_option autoImplicit false
variable {G:Gauge}{n k i r l p:ℕ}{b c d:ℝ}{X ι: Type}
variable (e:Oasis G)(E:∀ n,RackCore e.a e.M n)(x:G.ColorIndex)
open Trace Pigment Local
-- T selection. actual tournament opportunities at every funded stage marker order. Keep origin occupiers local. Epoch link before ALL testing.
variable {Z:Rival}{s t:ℝ≥0} {V: Cards→ bore G} {Q:ℕ→TableFee} {ν:Cover}{w:E4}
section
-- pollen pull all-address read
lemma nest_card {L:Side}(h: ‖w‖+(L.val:ℝ)⁻¹*4≤4)(f:Cards)(hp:Costs k f b)(hb:0≤b):Costs k (Cards.onRoute w (L.val:ℝ)⁻¹ f) b := fun i hi x hx=> (Cards.powCosts hp w (by positivity) h _ hi x hx).trans (mul_le_of_le_one_right hb (pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by exact_mod_cast (show 1 ≤ L.val from L.property))))) -- order Dol implicit?
-- generalize xloose
def newCoin (e:Oasis G) (k n i:ℕ)(d:ℝ):ℝ:= let η:=e.haloSpan i; let C:= max 0 (mountain G 1 (fun _=>1) n);
    e.xloose k i * Real.exp (2*η:ℝ) *((C*Real.exp d)*(Fintype.card (Dye G)*beamPrice η (e.Z i))^n)
lemma fair_coin (k n:ℕ)(d:ℝ):e.Fair fun i=> newCoin e k n i d:= by
    let h:e.Fair (fun i=> Real.exp (2*(e.haloSpan i):ℝ)):= ((e.fair_const (Real.exp 2) (Real.exp_pos _).le)).admits (fun i=>(Real.exp_pos _).le) (Eventually.of_forall fun i=> Real.exp_le_exp.mpr (by linarith only [show (e.haloSpan i:ℝ) ≤ 1 from NNReal.coe_le_coe.mpr (e.tent i)])); exact ((e.fair_loose k).mul h).mul ((e.fair_const _ (mul_nonneg (le_max_left 0 _) (Real.exp_pos _).le)).mul (((e.fair_const _ (Nat.cast_nonneg _)).mul (e.fair_beam e.fair_z)).pow n))
private lemma motor {G:Gauge}{b:ℝ} (k:ℕ)(hb:0≤ b)(z:ℝ): mountain G 1 (fun _=>b) k ≤ max 0 (mountain G 1 (fun _=>1) k)*b:= by
   refine le_trans (b:=mountain G 1 (fun _=>1) k*b) (?_) (mul_le_mul_of_nonneg_right (le_max_right ..) hb); unfold mountain; simp only [sum_mul,mul_one,mul_assoc]; rfl
private lemma mail {x:Candles G} (i:ℕ) (y:Dye G) (η:ℝ≥0): access (e.L i) η (((0:Cover),x)) (((0:Cover),y))= Real.exp (2*η:ℝ):= by
    have he: rent (e.L i) 0=0:= by symm; apply rent_unique; simp [Lattice.lift]
    change Real.exp (η*(↑(Laurent.size ((0:Cover)-rent (e.L i) 0))+2):ℝ)=_; rw [he,sub_zero]; simp [Laurent.size, mul_comm]
variable {P:Field (Fin k) (Node (Dye G))}{F:bore G}{m:ℕ}{y:Dye G}{z: Candles G}
-- y gauge.Shape rank.
lemma lot_fee {d:ℝ} (p k r n:ℕ) (h:i<n)(hd:0≤d)(hq:Preset e d ν i)(hc:0≤c) (hh:∀ t < k,Rest (terrain (e.ξ (i+1)) _) (0,y) (coil F p l t) c) : let V:=coil (migrated F ν) p l
    Rest (e.Bx r i) (0,y) (lifts (Barrage.Slope.nest (e.R i) G (e.vintage i n)) (Slope.lottery k G V)) ((newCoin e r k i d)*c):= by
    intro V; let σ:= e.ξ (i+1); let z:Candles G:= Sum.inr y; have hp (t:ℕ)(ht:t<k): Rest (terrain σ _) (0,y) (V t) (Real.exp d*c):= by unfold V; rw [coil_burst]; exact (staple ν (hh t ht)).ist (mul_le_mul_of_nonneg_right (luggage e hq hd) hc)
    let C':=max 0 (mountain G 1 (fun _=>1) k); have ht:0≤ Real.exp d*c:= mul_nonneg (Real.exp_pos _).le hc; have hV:Rest (terrain σ _) (0,z) (Slope.lottery k G V) (C'*(Real.exp d*c)):= (mountain_fee (B:=fun _=>Real.exp d*c) (e.ξ_one (i+1)) hp z).ist (motor k ht d); let t := e.haloSpan i; have he := hoist_price y (e.amplifies i n h) (e.z_pos i).le (e.reaches i) hV; have hA: access (e.L i) (e.haloSpan i) ( (0:Cover),z) ((0:Cover),y)=_:= mail (x:=z) e i y _ -- implicit
    apply (goes e r i he).ist; unfold newCoin; rw [show (e.R i).L=e.L i from rfl, hA]; exact le_of_eq (by unfold C'; ring)
-- ability probe occupants
structure Puppet (G:Gauge) (p:ℕ)(V:Cards→bore G):Prop where
     holds v: Mount (V v) p
     forecast (y:Dye G) f: ∃ σ U,0 < σ ∧ Price (V f) y σ U
lemma fluct (P: Puppet G p V)(h:Wealthy e E x Q){K:ℕ}(hm:i < m)(hk:k ≤ K)(hK:0<K)(f:Cards) (y:Dye G) (z:Cover)(hh:∀ t≤k, ∃ b,Rest (terrain (e.ξ (i+1)) _) (0,y) (coil (V f) p l t) b):
      (rentCall e E x i hm).spot K 0 (coil (V f) p l k) z k=
          printRun (wreath z (install (Origin.bleed G (e.vintage i m))) (coil (V f) p l k))-
          lifts (Slope.nest (e.R i) G (e.vintage i m)) (Slope.lottery k G (coil (migrated (V f) z) p l)) := by
    let F:=V f; obtain ⟨σ,U,hU,hX⟩:=P.forecast y f; have hM:Mount (migrated F z) p:=migrant z (P.holds f) hX; choose! W hW using hh; let T:= rentCall e E x i hm; let H:=h.launch i m hm; have hx: T.W.V=e.provisional E i m:=by unfold provisional; rw [dif_pos hm]; rfl
    let η:= e.ξ (i+1); let X:= coil (V f) p l; let Y:=coil (migrated (V f) z) p l; have hY (t:ℕ)(ht:t≤ k): Rest (terrain η _) (0,y) (Y t) (parcelY η z * W t):= by unfold Y; rw [coil_burst]; exact staple z (hW t ht)
    have ha : Row.strip (Origin.stretch T.P T.K G T.W.V) (e.haloSpan i) (1+e.Z i):= fun v α=> H.scope (Sum.inr v) α
    rw [pure_parade H (e.reaches i) (hW k le_rfl) (coil_mirror _ (P.holds f).incarnate l k) hk hK,orchid,orchid]
    rw [← coil_burst] -- if twice same?
    exact gauge_horizon (e.reaches i) (T.wake) T.W.governed H.glow H.ahead (e.bare_a i hm) (e.halo_pay i) (purse_pos ..).le ha (add_nonneg zero_le_one (e.z_pos i).le) hM hY -- order vary
end
variable {m y:ℕ}
/-- CP7 analytic estimate milestone. Per elementary entry at actual Orbit.K
Earlier `coil` ranks explicitly costed in exponent `U`
For lens use with `coil_tags`, `Throng`, `PMOM` & `Clear.across`. -/
theorem camp_stars {v:ℕ} (h:n+1-k≤r)(hv:n+1-k≤ v)(hz:Decked Z e)(d:ℝ)(hd:0≤d) : e.Fair (fun i=> newCoin e v k i d) ∧ ∀ᶠ i in atTop,∀ m:ℕ,∀ hi:i < m,∀ p l:ℕ,∀ F: Cards → bore G,Puppet G p F → let K(r:ℕ)(c:Cards):= coil (F c) p l r; ∀ Y:ℕ,k ≤ Y→ 0 < Y → IsLinearMap ℝ (K k) → Clear (K k) (n+1-k) → ∀ (b:ℝ),0≤b → ∀(c:ℝ),0≤c→ ∀ x':Dye G, ∀ z:Cover, rent (e.L i) z=0 → Preset e d z i → ∀ w:E4, ‖w‖+(↑(e.L i).val:ℝ)⁻¹*4≤4 → Weight (K k) r (e.Bx v (i+1)) x' b → (∀ k'<k,Weight (K k') r (terrain (e.ξ (i+1)) _) x' c)→ Weight (fun φ:Cards=> (rentCall e E x i hi).spot Y 0 (K k (rotate (L:=e.L i) z w φ)) z k) r (e.Bx v i) x' ((upright e Z n i)*b+(newCoin e v k i d)*c):= by
   refine ⟨fair_coin e _ _ _, ?_⟩; obtain ⟨Q,hQ,hP⟩:= pays e E x; filter_upwards [cheers (Z:=Z) v hz h hv] with i hi m hH p l F hF -- binder
   intro r' Y hY hF' hL hp b b0 c c0 x' z hy hZ w hw hb hC f a a0 hf; let Z':= Cards.onRoute w (e.L i).val⁻¹ f -- Nat val vs ℝ!
   let G':= F Z'; have ht := nest_card hw f hf a0; have hs k' (he:k' < k):= hC k' he Z' a a0 ht
   have hg : Rest (e.Bx v (i+1)) (0,x') (r' k Z') (b*a):= hb Z' a a0 ht; have hh':= lot_fee (F:=G') e (ν:=z) p k v m hH hd hZ (y:=x') (mul_nonneg c0 a0) (l:=l) hs; let H:=hi m hH (r' k) hL hp _ b0 x' x' z hy w hw hb f a a0 hf -- error binder W let. 
   change Rest _ _ ((rentCall e E x i hH).spot _ _ _ _ _) _; rw [fluct e E x (i:=i) (k:=k) (l:=l) hF hQ hH hY hF' Z' x' z ?_]; swap
   · intro t ht; by_cases hu:t<k; · exact ⟨c*a, hs t hu⟩
     rw [Nat.le_antisymm ht (by omega)]; exact ⟨b*a, hg.upto _ bath_terrace le_rfl⟩
   rw [add_mul,mul_assoc (newCoin e v k i d)]; exact (print_fee H).sub hh'
end YM.Contacts.Procession.Port

import YM.Contacts.Procession.Cycle
import YM.Planned.PRIMARY_INTEGRAL_295.Edens
/-! The polynomial-keeping canonical harmonic filter applies in every period of the analytic step. Can use truths on this representative via Slope & Health. No alterations to Rep.history. -/
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Procession.Pierian
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Sun Xenon Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Welcome Resetter Shuttle.Tide
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
open Tree FreeResolvent Draw PhysicalNext.RankCovariance Catch Hinges Lotus Welcome.Theater
open Barrage Barrage.Slope Barrage.Reserve Barrage.Reserve.Oasis Odor Odor.Winding Odor.Winding.Sales Port
open Planned.PrimaryIntegral295 Carrier
variable {G:Gauge}{n k i r l p j:ℕ}{b c d:ℝ}{X ι: Type}
variable (e:Oasis G)(E:∀ n,RackCore e.a e.M n)(x:G.ColorIndex)
-- all statements use the P from Actor, not stamping plot
-- canonical estimator on earlier calls after gauge replacement.Packs with stamps 
variable {P:MapPrices}{U:ℕ→ TableFee}{e}{w:E4}{Z:Rival}(h:Charter e.a.clock.kernel.penalty P)(ht:Led Z e P)
include h
lemma pick (l:List Axis) (hx:l.length ≤ e.J (i+1)-2) (n:ℕ): (advanceC (e.L i) (total e i n) l).strip (P.α (e.J (i+1))) (purse P (e.J (i+1))/((e.L i).val:ℝ)^(1+l.length)):= h.wealth _ _ (e.a.clock.adm _) (e.a.clock.adm _) (e.a.fits.mono (Nat.le_succ i)) (park e i n) _ hx
lemma trueCore (i n:ℕ): Row.strip (total e i n) (P.α (e.J (i+1))) (purse P (e.J (i+1))):= strip_mono (pick h [] (by simp) n (i:=i)) le_rfl (div_le_self (purse_pos ..).le (one_le_pow₀ (Nat.one_le_cast.mpr (e.L i).property)))
omit h 
include ht
lemma gleam (i:ℕ): e.haloSpan i ≤ rentCheque P (e.J (i+1)):= (ht.wealth i).width
include h
lemma bright (i n:ℕ): (Slope.nest (e.R i) G (total e i n)).strip (e.haloSpan i) (e.Z i):= strip_mono (P:=Slope.nest (e.R i) G (total e i n)) (succeeds (s:=rentCheque P (e.J (i+1))) (trueCore h i n) (gleam ht i) (purse_pos ..).le) le_rfl (ht.wealth i).span -- arg name?
open Pigment Local Trace Port
variable {F:bore G}{ν:Cover}{y:Dye G} {m:ℕ}{v:ℕ}
omit h ht
private lemma motor {G:Gauge}{b:ℝ} (k:ℕ)(hb:0≤ b)(z:ℝ): mountain G 1 (fun _=>b) k ≤ max 0 (mountain G 1 (fun _=>1) k)*b:= by
   refine le_trans (b:=mountain G 1 (fun _=>1) k*b) (?_) (mul_le_mul_of_nonneg_right (le_max_right ..) hb); unfold mountain; simp only [sum_mul,mul_one,mul_assoc]; rfl
private lemma mail {x:Candles G} (i:ℕ) (y:Dye G) (η:ℝ≥0): access (e.L i) η (((0:Cover),x)) (((0:Cover),y))= Real.exp (2*η:ℝ):= by
    have he: rent (e.L i) 0=0:= by symm; apply rent_unique; simp [Lattice.lift]
    change Real.exp (η*(↑(Laurent.size ((0:Cover)-rent (e.L i) 0))+2):ℝ)=_; rw [he,sub_zero]; simp [Laurent.size, mul_comm]
include h ht
lemma addon {d:ℝ} (p k r n:ℕ) (hk:i<n)(hd:0≤d)(hq:Preset e d ν i)(hc:0≤c) (hh:∀ t < k,Rest (terrain (e.ξ (i+1)) _) (0,y) (coil F p l t) c) : let V:=coil (migrated F ν) p l
    Rest (e.Bx r i) (0,y) (lifts (Barrage.Slope.nest (e.R i) G (total e i n)) (Slope.lottery k G V)) ((newCoin e r k i d)*c):= by
    intro V; let σ:= e.ξ (i+1); let z:Candles G:= Sum.inr y; have hp (t:ℕ)(ht:t<k): Rest (terrain σ _) (0,y) (V t) (Real.exp d*c):= by unfold V; rw [coil_burst]; exact (staple ν (hh t ht)).ist (mul_le_mul_of_nonneg_right (luggage e hq hd) hc)
    let C':=max 0 (mountain G 1 (fun _=>1) k); have ht0:0≤ Real.exp d*c:= mul_nonneg (Real.exp_pos _).le hc; have hV:Rest (terrain σ _) (0,z) (Slope.lottery k G V) (C'*(Real.exp d*c)):= (mountain_fee (B:=fun _=>Real.exp d*c) (e.ξ_one (i+1)) hp z).ist (motor k ht0 d); let t := e.haloSpan i; have he := hoist_price y (bright h ht i n) (e.z_pos i).le (e.reaches i) hV; have hA: access (e.L i) (e.haloSpan i) ( (0:Cover),z) ((0:Cover),y)=_:= mail (x:=z) (e:=e) i y _ -- implicit
    apply (goes e r i he).ist; unfold newCoin; rw [show (e.R i).L=e.L i from rfl, hA]; exact le_of_eq (by unfold C'; ring)
lemma fluct {V:Cards→bore G}(H: Puppet G p V)(hT:Wealthy e E x U){K:ℕ}(hm:i < m)(hk:k ≤ K)(hK:0<K)(f:Cards) (y:Dye G) (z:Cover)(hh:∀ t≤k, ∃ b,Rest (terrain (e.ξ (i+1)) _) (0,y) (coil (V f) p l t) b):
      (rentCall e E x i hm).spot K 0 (coil (V f) p l k) z k=
          printRun (wreath z (install (Origin.bleed G (total e i m))) (coil (V f) p l k))-
          lifts (Slope.nest (e.R i) G (total e i m)) (Slope.lottery k G (coil (migrated (V f) z) p l)) := by
    let F:=V f; obtain ⟨σ,U',hU,hX⟩:=H.forecast y f; have hM:Mount (migrated F z) p:=migrant z (H.holds f) hX; choose! W hW using hh; let T:= rentCall e E x i hm; let H':=hT.launch i m hm; have hx: T.W.V=e.provisional E i m:=by unfold provisional; rw [dif_pos hm]; rfl
    let η:= e.ξ (i+1); let X:= coil (V f) p l; let Y:=coil (migrated (V f) z) p l; have hY (t:ℕ)(ht:t≤ k): Rest (terrain η _) (0,y) (Y t) (parcelY η z * W t):= by unfold Y; rw [coil_burst]; exact staple z (hW t ht)
    have ha : Row.strip (Origin.stretch T.P T.K G T.W.V) (e.haloSpan i) (1+e.Z i):= fun v α=> H'.scope (Sum.inr v) α
    rw [pure_parade H' (e.reaches i) (hW k le_rfl) (coil_mirror _ (H.holds f).incarnate l k) hk hK,orchid,orchid]
    rw [← coil_burst] -- if twice same?
    exact gauge_horizon (t:=rentCheque P (e.J (i+1))) (e.reaches i) (awakeV e hm) T.W.governed H'.glow H'.ahead (trueCore h i m) (gleam ht i) (purse_pos ..).le ha (add_nonneg zero_le_one (e.z_pos i).le) hM hY -- order vary
end YM.Contacts.Procession.Pierian

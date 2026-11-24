import YM.RGGapR2.Rough
import YM.MergeProof.Arbol
/-! Rough close-window pricing without requiring separated centers *during*
the steps. Each step contraction of marker radii with the actual probe,
exponent restored on both connected-log and attached components
(nonconstant-mode representation only). Reading estimates on full signed
coefficients before root. Based on Arbol.vista/sail; powers in terminal bound
require actual compatible replications. Not an estimate for the absolute gas
on individual fields after division.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGGapR2.Rough
open Function Finset Filter Lattice Wilson RG MeasureTheory Push Local Extra.Histories PhysicalNext.Repeat Lotus Merge Merge.Palette Marker Overlay
open MergeProof MergeProof.Menu MergeProof.Accent Extra.Multi GridApprox.Nil Extra.Trajectories Planned.GuardedAtom
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {V : Type}[DecidableEq V][Fintype V]{B:Census V}{G:Gauge}{n:Side}
set_option quotPrecheck false
set_option maxHeartbeats 1800000
section
variable {U:Config G n}{q:Finset V} {p:Support n}{F:Config G n→Poly B}{o:V→Site n}{t:ℝ}
lemma located (h:Borne o p F t)(he:(F U).part B.quiet=0)(hF:F U≠0) : ∃ j,o j∈p :=by
    have hx:∃ i,(F U).part i≠0:= Classical.byContradiction (fun ht=> hF (by ext i; exact not_not.mp (fun he=> ht ⟨i,he⟩)))
    obtain ⟨i,hi⟩:=hx; have hh : i.val.Nonempty:= Finset.nonempty_iff_ne_empty.mpr (fun hj=>hi ((congr_arg ((F U).part) (show i=B.quiet from Subtype.ext hj)).trans he))
    obtain ⟨j,hj⟩:=hh; exact ⟨j,h.place i U hi (mem_image_of_mem _ (show j∈i.val from hj))⟩
variable {A:Rep G n}{F:Config G n→Poly B}{r:V→ℝ}{e d a x:ℝ}
lemma steerAll (U:Config G n) (hr:∀ i,0< r i)(he:0≤e)(hx:Freight A B F o r e x)(h:A.activities.Valid A.p t a): Poly.price r (F U) ≤ Real.exp (A.exponent U+Fintype.card V*(2*x)+Fintype.card (Site n)*a) :=by
    obtain ⟨H,K,hH,hB,hS,hY⟩:=hx
    have h₁ : ∑ i,Poly.price r (bar A.activities B U i) ≤ Fintype.card (Site n)*a:=by
        apply Accent.harvest (Y:=Config G n) (F:=fun i U=>bar A.activities B U i) (J:=Site n) (vacant A.activities _ B h r hr) hr A.p.exponent_pos.le U id; intro i hi
        have ht:= (granular A.activities _ B (o:=o) h i).permits U hi; obtain ⟨j,hj⟩:=ht.2.1.mono ht.2.2; exact ⟨j,hj⟩
    have hu:∑ i,Poly.price r (K i U) ≤ Fintype.card V*x:= by exact Accent.harvest hS hr he U o (fun i hi=> located (hH.flag i|>.1.toBorne) ((hH.flag i).2 U) hi)
    have hV:∑ i,Poly.price r (H i U) ≤ Fintype.card V*x:=by exact Accent.harvest hB hr he U o (fun i hi=> located (hH.exp i).toBorne ((hH.exp i).sil U) hi)
    let Z i:= bar A.activities B U i+K i U; let Y:=∑ i,H i U; let N:ℝ:= Fintype.card V; let m:ℝ:=Fintype.card (Site n)
    have hz : ∑ i, Poly.price r (Z i) ≤ m*a + N*x:=by apply (Finset.sum_le_sum fun i _=> Poly.addition hr _ _).trans; rw [Finset.sum_add_distrib]; exact add_le_add h₁ hu
    have hp : Poly.price r Y ≤ N*x:=le_trans (Poly.batch hr Finset.univ (fun i=>H i U)) hV
    rw [show F U= (Real.exp (A.exponent U):ℂ) • (Poly.pass Y*field Z (flags A.p.threshold U)) from (congr_fun hY _),Poly.adapted, Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]
    refine mul_le_mul_of_nonneg_left (Poly.multiplication hr (Poly.pass Y) _) (Real.exp_pos _).le |>.trans ((mul_le_mul_of_nonneg_left (mul_le_mul ((Poly.pass_budget hr _).trans (Real.exp_monotone hp)) ((grid_pay Z _ hr).trans (Real.exp_monotone hz)) (Poly.nonnegative hr _) (Real.exp_pos _).le) (Real.exp_pos _).le).trans_eq ?_)
    rw [← Real.exp_add _ (m*a+N*x),← Real.exp_add]; change _ = Real.exp (A.exponent U+N*(2*x)+m*a); congr 1; ring
end
open YM.PhysicalNext.Repeat.Legato YM.PhysicalNext.Repeat.Legato.Bandage
variable {A:History G} (N k m p:ℕ)
local notation "P"=> A.levels.budget
local notation "R"=> A.rep N p
local notation "D" j => Config G (A.S.side j p)
variable {X: Config G (A.S.side k p) → Poly B}{D':∀ N p m:ℕ,m<N→ GaugeDoor (A.rep N p (m+1)) (A.rep N p m)}
variable {u:ℕ→ℝ} {r:ℕ→ℕ}
-- relative radius at i wrt terminal rough-stop n
-- given at N: u_N; after one step at most renal i multiplier.down = hat^-2*(previous)
def ticket (A:History G)(n i:ℕ)(x:ℝ):ℝ:=((A.levels.clock.hatBeta n)^2)⁻¹^(n-i) * x
include k m
lemma ticket_pos {s:ℝ}(h:s>0):0<ticket A k m s:=mul_pos (pow_pos (inv_pos.mpr (pow_pos (zero_lt_one.trans (A.levels.fits.delayed _)) _)) _) h
lemma ticket_le {x:ℝ}(h:G.Simple)(hx:0 < x)(he:m<k) : ticket A k m x ≤ renal A.levels m * ticket A k (m+1) x:=by
    let Y:=A.levels.clock.hatBeta; unfold ticket; rw [show k-m = k-(m+1)+1 by omega,pow_succ',mul_assoc]
    unfold renal Mallow.probe; rw [Real.rpow_neg ((zero_lt_one.trans (A.levels.fits.delayed _)).le),Real.rpow_two]
    exact mul_le_mul_of_nonneg_right (inv_le_inv₀ (pow_pos (zero_lt_one.trans (A.levels.fits.delayed _)) _) (pow_pos (zero_lt_one.trans (A.levels.fits.delayed _)) _) |>.mpr (pow_le_pow_left₀ (zero_le_one.trans (A.levels.fits.delayed _).le) (WilsonStartup.Timing.hat_mono A.levels (Gauge.slopeConstant_pos h).le he) _)) (ticket_pos (A:=A) k (m+1) hx).le
variable {o:∀ j:ℕ,V→Site (A.S.side j p)}(h:A.Selected)(hh:Moonlit A r (renal A.levels) u D') (he:m ≤ k)(hN:k ≤ N)
variable (hm:∀ i (_hi:m ≤ i) (_hk:i<k), (A.levels.clock.op i p).ratio.parent ∘ o (i+1) = o i ∧ Occupancy (o i) (r i))
include N hN h p
include hh hm
lemma transit {w:V→ℝ}(hG:G.Simple)(hI:∀ i,0< w i)(hX:Freight (R k) B X (o k) w ((P k).supportExponent-4) 1)(i:ℕ)(hi:i ≤ k)(hk:m ≤ i): Freight (R i) B (gust A N p k X i hi) (o i) (fun j=>ticket A k i (w j)) ((P i).supportExponent-4) 1:=by
    induction hi using Nat.decreasingInduction with
    | self=> rw [gust_base]; convert hX using 1; ext i; rw [ticket,Nat.sub_self,pow_zero,one_mul]
    | of_succ i hi ih=>
      have hy:=ih (hk.trans i.le_succ)
      have hN':i<N:=hi.trans_le hN; obtain ⟨y,z,G',hY⟩:= hh.days N p i hN'
      obtain ⟨hA,hB⟩:= hm i hk hi
      rw [gust_step A N p k X hi, ←hA]; rw [←hA] at hB
      have hc:=Rough.reducedStep A r N i p h hN' hY G' (fun j=> ticket_pos k (i+1) (hI j)) (fun j=> ticket_pos k i (hI j)) hy le_rfl hB (fun j=>ticket_le k i hG (hI j) hi)
      obtain ⟨U,K,h',hv,hs,hT⟩:=hc
      exact ⟨U,K,h',hv.shrink (by linarith : (P i).supportExponent-4 ≤ (P i).supportExponent) le_rfl (fun j=>(ticket_pos k i (hI j))),hs.shrink (by linarith : (P i).supportExponent-4 ≤ (P i).supportExponent) le_rfl (fun j=>ticket_pos k i (hI j)),hT⟩
omit hm hh N k p
variable (A)
def price := Real.exp ((Fintype.card (Site (A.S.side m p)):ℝ) * Vac.treasury A.levels m +(Fintype.card V:ℝ)*(2:ℝ))
variable {A}
variable (mode:B.Mode)(v:V→ ℝ)(Z: Config G (A.S.side m p)→Poly B)
variable (A)
def fixed:= (∫ U, (Z U).part mode∂prior G _) / ((∫ U,(R m).eval U∂prior G _):ℝ) -- coercion ℝ→ℂ?
variable {A}
omit k
include N p h he hN
omit he hN
lemma paid (ht:m≤N) {e:ℝ} {y:V→ Site (A.S.side m p)}(hy:Integrable Z (prior G _))(hX:Freight (R m) B Z y v e 1) (hr:∀ i,0<v i)(hz:0 ≤ e): 
    ‖fixed A N m p mode Z‖ * Poly.toll v mode ≤ price (V:=V) A m p:=by
      let K:=Fintype.card V; let S:=A.rep N p m; have hT:= h.represents N p m ht
      let Y':=A.levels.clock; let gas:=A.levels.params m; let Δ:=Real.exp (S.scalar + Bands.fine (Fintype.card V) S 0 0 (2*1) 1 gas.paths (Y'.loopCap m) (Y'.allowance m) (Y'.forcedAllowance m))
      have hp : Integrable (fun U=>(Z U).part mode) (prior G _):= ((Poly.get mode).restrictScalars ℝ).integrable_comp hy
      have hc:=Overlay.beta_positive h (p:=p) ht
      have hζ:=zero_lt_one.trans (A.levels.fits.delayed m); let z:=A.levels.clock.hatCoupling m; have hP : 0<z:= inv_pos.mpr (Real.sqrt_pos.mpr hζ)
      have hδ : z ≤ S.p.threshold:=by rw [show S.p=_ from hT.vac];exact le_mul_of_one_le_right hP.le (Real.one_le_exp (sq_nonneg _))
      have hV (U:D m): Poly.price v (Z U) ≤ Δ:=by
          refine (Rough.steerAll U hr hz hX hT.good.labels).trans (Real.exp_monotone ?_); unfold Bands.fine; linarith only [S.exponent_hi hT.good hc.le U] -- replace
      let I:=prior G (A.S.side m p); let Y(U:D m) := (Z U).part mode
      have he' : ‖(∫ U,Y U ∂I)‖ ≤ Δ / Poly.toll v mode:=by apply (norm_integral_le_integral_norm _).trans; calc
       _ ≤ ∫ _ : D m, Δ/Poly.toll v mode ∂I := integral_mono hp.norm (integrable_const _) (fun U=> (le_div_iff₀ (Poly.worth hr _)).mpr (le_trans (le_of_eq (mul_comm ..)) ((Poly.member hr ..).trans (hV U))))
       _ = _:=by unfold I; simp
      have hO:= S.denominator hT.good hc.le z hP hδ (History.nonnegative A h _ _ _ ht)
      let A':= Real.exp (Bands.finalBill K S z 0 0 (2*1) 1 gas.paths (Y'.loopCap m) (Y'.allowance m) (Y'.forcedAllowance m))
      refine le_trans (b:=A') ?_ ?_
      · rw [fixed,norm_div,Complex.norm_real, Real.norm_of_nonneg (lt_of_lt_of_le (Real.exp_pos _) hO).le,div_mul_eq_mul_div,div_le_iff₀ (lt_of_lt_of_le (Real.exp_pos _) hO)]; refine ((le_div_iff₀ (Poly.worth hr _)).mp he').trans ((le_trans (b:=A'*Real.exp _) (by apply le_of_eq; rw [show A'=Real.exp (Bands.finalBill K _ _ _ _ _ _ _ _ _ _) from rfl,←Real.exp_add]; unfold Δ K Bands.fine Bands.finalBill; congr 1; rw [show Fintype.card (Edge (Site (A.S.side m p)))=Fintype.card (Site (A.S.side m p))*4 by simp [Edge,Axis]];push_cast;ring) (mul_le_mul_of_nonneg_left hO (Real.exp_pos _).le)))
      apply Real.exp_monotone
      convert! Vac.suffices_bill (p:=p) h ht K (0:ℝ) (0:ℝ) (2*1) 1 using 1; -- print
      unfold K;ring
include hm k hh he hN
lemma during(hG:G.Simple)(hr:∀ i,0<v i)(hX:Freight (R k) B X (o k) v ((P k).supportExponent-4) 1)(hi:Integrable X (prior G _)) :
   ‖fixed A N k p mode X‖ * Poly.toll (fun i=>ticket A k m (v i)) mode ≤ price (V:=V) A m p:=by
     have ht:=he.trans hN; have hf := transit N k m p h hh hN hm hG hr hX _ he le_rfl
     let z:=gust A N p k X m he; have hz:Integrable z (prior G _):= gust_live A N p k X hi he
     have hg:4 ≤ (P m).supportExponent := by have h':= hh.days (m+1) p m m.lt_succ_self |>.choose_spec.choose_spec; linarith only [h'.2.exp.1] -- placeholder
     have hv:= paid N m p h mode (fun i=>ticket A k m (v i)) z ht hz hf (fun i=>ticket_pos k m (hr i)) (by linarith only [hg])
     have hB:(∫ U, z U∂prior G _)=(∫ U, X U∂prior G _):=gust_sum A N p k X hi he
     change (‖fixed A N m p mode z‖ * Poly.toll _ mode ≤ price (V:=V) A m p) at hv
     apply le_trans (le_of_eq ?_) hv; unfold fixed; rw [History.partition_eq A h N p k hN, History.partition_eq A h N p m ht,show (∫ U,(X U).part mode∂prior G _)=_ from (((Poly.get mode).restrictScalars ℝ).integral_comp_comm hi), show (∫ U,(z U).part mode∂prior G _)=_ from (((Poly.get mode).restrictScalars ℝ).integral_comp_comm hz)] -- search names
     exact congr_arg (fun x => ‖(Poly.get mode x)/ ↑(partition G (A.S.side N p) (A.β N p N))‖ * _) hB.symm
end YM.RGGapR2.Rough

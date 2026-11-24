import YM.FVA2.StampCost
/-!
# The actual unmasked full-cover interaction invoices

path weights with log correction and Haar.Clocks `z` with leading one (used precisely on that trajectory) here.
No masks.Evaluate the actual log at each real vector x.X relates.Drop.Matcher.Angular fields.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.FVA2.CityHistory.Legacy
open Function Filter Set Topology MeasureTheory Lattice Gauge RG _root_.YM.Wilson
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested PertExtension.Series.Radial
open FormalOPE.RG10 FormalOPE.RG10.Inherit FormalOPE.RG10.OpenSlots FormalOPE.RG10.MarkovChain.Warp FormalOPE.RG10.MarkovChain.Router FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Stack FormalOPE.RG10.MultiGauge.Splice
open Precision GaussianScore RGComparison.Core16 RGComparison.Core16.Descent Tree Exterior Push.BetaTransport Tandem Luggage Fares
open MeasureTheory.Measure (IsAddHaarMeasure)
open PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{c f n:Side}
-- use the log-form identity; independent of proof choices above these germs.
section
variable {E K:Type}[NormedAddCommGroup E][NormedAddCommGroup K][NormedSpace ℝ E][NormedSpace ℝ K][FiniteDimensional ℝ E][FiniteDimensional ℝ K]
omit [FiniteDimensional ℝ E][FiniteDimensional ℝ K] in
lemma boost_compose0 (p:E→ₗ[ℝ] K)(L: Ticket K)(x:E): Stack.read x (boost p L)= Stack.read (p x) L:= caught p L x -- order uncertain
lemma boost_coeff2 (p:E→ₗ[ℝ] K)(f:K→ℝ)(hf:ContDiffAt ℝ ω f 0): boost p (C (coeff 2 (rise f)))= C (coeff 2 (rise (f ∘ p))):= by rw [← FormalOPE.RG10.MarkovChain.Vault.climbing p (hf.of_le le_top), boost, PowerSeries.map_C, coeff_map ]
lemma flat_boost (p:E→ₗ[ℝ] K){L:Ticket K}(h:constantCoeff L=0): constantCoeff (boost p L)=0:= by unfold boost; rw [← coeff_zero_eq_constantCoeff_apply,coeff_map,coeff_zero_eq_constantCoeff_apply,h,map_zero ]
lemma upright_pay (w:PowerSeries ℝ){g:E→ℝ}(he:Radial.Stationary g)(hw:constantCoeff w=1): X^2*(pay w g - C (coeff 2 (rise g))) = -(carry w * rise g):= by
     obtain hv:= price_charge w g he; rw [show roll (term w 0)= (1:Ticket E) from ?_,one_mul ] at hv; exact hv.trans (by ring); unfold term roll; rw [coeff_zero_eq_constantCoeff_apply, hw,map_one,map_one]
end
section
variable (S:StepData c f)(T:Forest S.ratio)(b:S.Choices)(h:S.patch.Branches S.kernel G)
include h
lemma price_stat : Radial.Stationary ( tax S T b (G:=G) ) := by
    apply Inherit.stable (tax_hot S T b h);
    · unfold tax; -- flat
      rw [Prod.fst_zero,Prod.snd_zero,← inserts,identity_zero, map_zero,identity_zero ]; -- fails order
      simp [tagEnergy,noiseEnergy,linkEnergy,Push.settled S h]
    intro v; unfold tax tagEnergy; exact (energy_estimate S (G:=G) _).nonneg _
end

lemma born_hot (G:Gauge)(n:Side): ContDiffAt ℝ ω (bareF G n) 0:= by
    let D:= Descent.nil (top:=n); let t:D.Tags:= (); let F:= consume D t (G:=G) 1; let M:= ContinuousLinearMap.inr ℝ ( Coordinates G D ) ( Pins G n ); rw [ show bareF G n=F ∘ M from funext (fun x=> (one_mul (bareF G n x)).symm) ]; exact ContDiffAt.comp (f:=M) _ ( thermal D t trivial _ ) M.contDiff.contDiffAt
lemma bare_zero (G:Gauge)(n:Side): bareF G n 0=0:= by
    let D:=Descent.nil (top:=n); let t:D.Tags:= (); obtain he:= thermal_zero D (G:=G) t trivial 1; change 1 * bareF G n 0= 0 at he; simpa using he
lemma top_ok (G:Gauge)(n:Side) : Radial.Stationary (bareF G n):= Inherit.stable (born_hot G n) (bare_zero G n) (fun x=> energy_nonneg (expLinks G _ x))

variable {d:Descent n c}
-- β exponent and X-book. Used core:H tess; unpack recursively for the full proof
abbrev κ (d:Descent n c) (G : Gauge) := Ticket (SpaceF G d)
def moneyX {c:Side}(d:Descent n c)(t:d.Tags)(z:ℕ→PowerSeries ℝ) : κ d G :=
    match d with
    | .nil => boost (LinearMap.snd ..) (carry (z 0) * rise (bareF G n))
    | .push S T d' => boost (partΧ G S T d') (moneyX d' t.2 (parentZ z)) + boost (partΥ G S T d') (carry (z 1) * rise (tax (G:=G) S T t.1))

def entryPay {c:Side}(d:Descent n c)(t:d.Tags)(z:ℕ→PowerSeries ℝ): Ticket (SpaceF G d):=
    match d with
    | .nil=> boost (LinearMap.snd ..) (pay (z 0) (bareF G n))
    | .push S T d' => boost (partΧ G S T d') (entryPay d' t.2 (parentZ z)) + boost (partΥ G S T d') (pay (z 1) (tax (G:=G) S T t.1))

lemma startPay (h:d.OK G)(t:d.Tags)(z:ℕ→PowerSeries ℝ): constantCoeff (entryPay (G:=G) d t z)=0:= by
    induction d generalizing z with
    | nil=> rw [entryPay]; exact flat_boost _ (stipend _ _ (top_ok ..))
    | push S T d ih=> rw [entryPay,map_add,flat_boost _ (ih h.2 ..),flat_boost _ ( stipend _ _ (price_stat S T t.1 h.1) ),add_zero]

-- `moneyX d t 1` precisely path-ordinary Wilson-price Taylor expansion. Then `totalPay` identity with `X` unbounded phase restored. orientation of commutativity. Lambda.
lemma consume1_l (S:StepData c f)(T:Forest S.ratio)(d:Descent n f)(t:(Descent.push S T d).Tags): consume (G:=G) (Descent.push S T d) t 1 = consume d t.2 1 ∘ partΧ G S T d + tax S T t.1 ∘ partΥ G S T d := by
     rcases t with ⟨t,H⟩;  -- t binder syntax maybe fails
     exact funext (fun x=> (at_step S T d H t 1 x (G:=G)).trans (congr_arg₂ (·+·) rfl (one_mul _)) )
lemma consume0 (n:Side) (t:(Descent.nil (top:=n)).Tags) : consume (G:=G) (Descent.nil (top:=n)) t 1 = bareF G n ∘ LinearMap.snd ℝ _ _:= funext (fun i=> one_mul _)

-- notation t.1 after case uses destruct.Pair.Ease.RG.Some points.
lemma ordinary (h:d.OK G)(t:d.Tags) : moneyX d t (G:=G) 1 = rise (consume d t 1) := by
     induction d with
     | nil=> rw [ moneyX,Pi.one_apply,map_one, one_mul, consume0,FormalOPE.RG10.MarkovChain.Vault.climbing _ ((born_hot ..).of_le le_top)]
     | push S T d ih=>
         rw [moneyX, show parentZ 1=1 from rfl, consume1_l, ih h.2, Pi.one_apply, map_one,one_mul]; simp_rw [ FormalOPE.RG10.MarkovChain.Vault.climbing (partΧ G S T d) ((thermal d t.2 h.2 1).of_le le_top), FormalOPE.RG10.MarkovChain.Vault.climbing (partΥ G S T d) ((tax_hot S T t.1 h.1).of_le le_top)]; exact (ExactTower.up_add ((leaned _ (thermal d t.2 h.2 1)).of_le le_top) ((leaned _ (tax_hot S T t.1 h.1)).of_le le_top)).symm

lemma boostXcharge {E K:Type} [NormedAddCommGroup E][NormedAddCommGroup K][NormedSpace ℝ E][NormedSpace ℝ K][FiniteDimensional ℝ E][FiniteDimensional ℝ K](p:E→ₗ[ℝ] K)(A B:Ticket K) (R:Ticket K) (he:X^2*(A - C (coeff 2 B))=-R): X^2*(boost p A-C (coeff 2 (boost p B)))=-boost p R:= by obtain ht:= congr_arg (boost p) he; rw [map_mul,map_neg,map_sub,map_pow,show (boost p) X=X from PowerSeries.map_X _] at ht; refine Eq.trans ?_ ht; unfold boost; rw [ PowerSeries.map_C,coeff_map ]

-- the *exact Kinetic* log equation on the path bill.TRUE for all z with leading 1 (upper `Pamp`). Need additional strong$ if wanting ward budget.
def SoundZ (z:ℕ→PowerSeries ℝ): Prop:= ∀ i, constantCoeff (z i)=1
variable (h:d.OK G)(t:d.Tags)(z:ℕ→PowerSeries ℝ)(hs:SoundZ z)
include h hs in
theorem issueZ : X^2*((entryPay d t z (G:=G))- C (coeff 2 (rise (consume d t 1 (G:=G)))))= - moneyX d t z:= by
    rw [ ← ordinary h ]; induction d generalizing z with
    | nil=>
         rw [ entryPay,moneyX,moneyX,Pi.one_apply,map_one, one_mul ]; exact boostXcharge _ _ _ _ ( upright_pay (z 0) (top_ok ..) (hs 0) )
    | @push c f S T d ih=>
         let hx:= ih h.2 t.2 (parentZ z) (fun i=> hs (i+1)); let U:= boostXcharge (partΧ G S T d) _ _ _ hx; let V:= boostXcharge (partΥ G S T d) _ _ _ ( upright_pay (z 1) (price_stat S T t.1 h.1) (hs 1)); rw [ entryPay, moneyX,moneyX, Pi.one_apply,map_one,one_mul,map_add,map_add, neg_add,← U,← V,show parentZ 1=1 from rfl ]; ring -- rw order

end YM.FVA2.CityHistory.Legacy

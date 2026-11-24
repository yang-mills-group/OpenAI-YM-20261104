import YM.Integration.WilsonThermometerMixedShoulder
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerMixedProgram
open Function Finset Lattice Wilson RG Ac Marker QuadraticLocal Push Push.Corrected Push.AbsoluteSums
open RG3 RG3.Ink Ovens Ovens.Pipes Progress.DirectedRecipe QuadraticLocal.Fusion QuadraticLocal.Fusion.Attached
open QuadraticLocal.Earn QuadraticLocal.Affinity QuadraticLocal.Tint
open WilsonThermometerMixedGallery WilsonThermometerMixedAmplitude
open scoped Classical BigOperators
variable {R:Marker.Census (Fin 3)} {G:Gauge} {n:Side} {P:Rep G n} {o:Passport n (Fin 3)}
  {X ι μ:Type} {w:Fin 3→ℝ} {a e k M:ℝ} {B:ℕ} {p:BudgetPoint}

/-- The selected endpoints use the identical passport, old hard addresses and source names.
Every freshly rendered regular word is held fixed. -/
def intake (c:ℂ)(reg:ι→R.Mode→Prop)(owners:ℕ→R.Mode→Prop)(Z:Incoming o P X ι R):Incoming o P X ι R:=
  ⟨lamps c reg Z.old,hard c owners Z.hard⟩

def prepared (head:Lamps X μ G P.p o.origin R)(Z:Incoming o P X ι R):Gallery X (μ⊕ι) o.origin P R:=
  ⟨head.join Z.old,Z.hard⟩

theorem sheet (head:Lamps X μ G P.p o.origin R)(Z:Incoming o P X ι R)
    (reg:ι→R.Mode→Prop)(owners:ℕ→R.Mode→Prop){q T:ℂ}(inverse:q*T=1)
    (hw:∀v,0<w v) (old:Z.old.Paid w P.p.B P.p.supportExponent e)
    (bank:Z.hard.Paid w P.p.B P.p.supportExponent k)
    (x:X)(U:Config G n)(degree:ℝ)(headPrice:head.Paid w P.p.B P.p.supportExponent degree):
    Line q ((prepared head (intake 0 reg owners Z)).density x U)
      ((prepared head Z).density x U) ((prepared head (intake T reg owners Z)).density x U):=by
  let E:=Z.old
  let s:=WilsonThermometerMixedShoulder.picked E reg
  have small:=WilsonPrecontactSeparatedLamps.charged E s old
  have lo:=WilsonThermometerMixedShoulder.regular E reg 0 hw old small
  have high:=WilsonThermometerMixedShoulder.regular E reg T hw old small
  have zk:=WilsonThermometerMixedShoulder.forced Z.hard owners 0 bank
  have yk:=WilsonThermometerMixedShoulder.forced Z.hard owners T bank
  have ha:=P.p.exponent_pos.le
  apply scaled
  apply WilsonThermometerMixedAmplitude.product
  · apply WilsonThermometerMixedAmplitude.passed
    apply series _ _ _ ((Lamps.joinPaid headPrice lo).sums ha hw x U) ((Lamps.joinPaid headPrice high).sums ha hw x U)
    intro i
    cases i with
    | inl i=>
      simp only [Lamps.pureJoin]
      exact same _
    | inr i=>
      simp only [Lamps.pureJoin']
      change Line q ((lamps 0 reg E).frame i x U) (E.frame i x U) ((lamps T reg E).frame i x U)
      rw [WilsonThermometerMixedGallery.sheet,WilsonThermometerMixedGallery.sheet]
      exact amplitude _ _ inverse
  · apply series _ _ _ (Hard.packet_summing _ zk ha hw x U) (Hard.packet_summing _ yk ha hw x U)
    intro cover
    by_cases adm:P.activities.admissible P.p U cover
    · simp only [packet,if_pos adm];exact products _ _ _ _ (fun i _=>amplitude _ _ inverse)
    · simp only [packet,if_neg adm];exact same _

/-- At the restored marker radius only the selected occurrences spend the enlarged tariff. -/
theorem selected (L:Lamps X ι G p o.origin R) (c:ℂ)
    (wallet:(WilsonPrecontactSeparatedLamps.portion L (WilsonPrecontactSeparatedLamps.mixed L)).Paid w B a M):
    (WilsonPrecontactSeparatedLamps.portion (lamps c (fun _ _=>True) L)
      (WilsonPrecontactSeparatedLamps.mixed L)).Paid w B a (‖c‖*M):=by
  obtain ⟨f,nn,rows,due⟩:=wallet.budget
  refine ⟨fun j=>‖c‖*f j,fun j=>mul_nonneg (norm_nonneg _) (nn j),?_,?_⟩
  · intro j t v hv
    have chosen:1<(L.mode j.val).val.card:=j.property
    change p.supBounds v (L.ground j.val)
      (rent c (fun _=>True) (L.mode j.val) • L.nominal t j.val) _
    rw [show rent c (fun _=>True) (L.mode j.val)=c from if_pos ⟨chosen,trivial⟩]
    exact Next.Foundations.bound_smul c (rows j t v hv)
  · intro v
    have h:=budget_scale (norm_nonneg c) (due v)
    convert h using 1
    funext i
    by_cases mem:v∈L.ground i.val
    · change (if v∈L.ground i.val then Poly.toll w (L.mode i.val)*(‖c‖*f i)*Real.exp (a*coverNumber B (L.ground i.val)) else 0)=_
      rw [if_pos mem]
      change _=‖c‖*(if v∈L.ground i.val then Poly.toll w (L.mode i.val)*f i*Real.exp (a*coverNumber B (L.ground i.val)) else 0)
      rw [if_pos mem];ring
    · change (if v∈L.ground i.val then _ else 0)=‖c‖*(if v∈L.ground i.val then _ else 0)
      simp only [if_neg mem,mul_zero]

section Agent
variable {D:Fin 3→Type} [∀v,AddCommGroup (D v)] [∀v,Module ℝ (D v)]
variable (A:∀v,Set (D v))(K:∀v,Submodule ℝ (D v))
theorem admissible (Z:Incoming o P (Wallet A) ι R)(reg:ι→R.Mode→Prop)(owners:ℕ→R.Mode→Prop)(c:ℂ)
    (rows:Taut o.support A K Z.old)(flags:Crown o.support A K Z.hard):
    Taut o.support A K (intake c reg owners Z).old ∧ Crown o.support A K (intake c reg owners Z).hard:=by
  refine ⟨⟨rows.house,?_⟩,⟨?_⟩⟩
  · intro i U
    let k:=rent c (reg i) (Z.old.mode i)
    exact (rows.adv i U).linear ((LinearMap.mulLeft ℂ k).restrictScalars ℝ)
  · intro i U
    constructor
    intro s
    have h:=(flags.lesson i U).each s
    let k:=rent c (owners i) s
    refine ⟨h.advice.linear ((LinearMap.mulLeft ℂ k).restrictScalars ℝ),fun t live v hv=>?_⟩
    exact h.announces t (right_ne_zero_of_mul live) v hv
end Agent

end YM.Integration.WilsonThermometerMixedProgram

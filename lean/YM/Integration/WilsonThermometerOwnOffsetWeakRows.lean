import YM.Integration.WilsonThermometerIntrinsicRoster
import YM.MergeProof.West.Pamu
import YM.MergeProof.Garnet

/-! The complete source in the original weak detector at the parent of an
independently placed thermometer. The reporting singleton has its prescribed
physical germ. The mixed regular and forced rows retain their supports. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerOwnOffsetWeakRows
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open Next.Rank Edition Baler Value Glyph Thirst Alarm
open Trace.Physical Push.Local
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open WilsonThermometerOwnOffsetTale WilsonThermometerOwnOffsetNectar WilsonThermometerOwnOffsetRadii
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {N p k d : ℕ}
local notation "P" => R.family.path.rep N p k
local notation "B" => WilsonThermometerOffsetLedger.cash R

theorem singleton {V : Sight R.family d p} {r : Emblems R.family d}
    (z : Site (R.family.side N p)) (hk : k≤N) (y : Palette R.family d)
    (H : Enrolled R.makes R.doors B k N p d (digits R N p z) V r) :
    let o := site R hk z
    let E := state (k:=k) R V r y z k
    ∃ X : Coefficient (R.family.labels.level d) (R.family.side k p),
      Germ.projection (R.family.labels.level d) R.family.params (P).p.threshold 0 X=y (primaryLetter d) ∧
      X.Format 0 R.family.params P ∧ X.remBound 0 P (kappa R.family.path k) (B d k*size y) ∧
      View.Signpost P (1,false) o (invoice X 0 (R.family.localSection d) P) E := by
  intro o E
  let t := primaryLetter d
  obtain ⟨u,hp⟩ := (H.legal k le_rfl hk).capacity0 y
  rcases hp with @⟨X,F,fee,b,tail,cert,wallet,assembled,hx,hy,financed⟩
  have spare : fee t ≤ B d k*size y := ((Finset.single_le_sum
    (fun j _ => rem_nonneg (wallet j)) (Finset.mem_univ t)).trans
    (le_add_of_nonneg_right tail.nonneg)).trans financed
  have filed : V k y (line t) = invoice (X t) 0 (R.family.localSection d) P :=
    (congrArg (fun S : Tape G (R.family.side k p) => S (line t)) assembled.symm).trans
      (together_line X F tail t)
  refine ⟨X t,(congrFun hy t).symm,cert t,rem_mono (wallet t) spare,?_⟩
  have nz : (R.family.S.a k:ℂ)^d≠0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (R.family.S.a_pos k).ne')
  have eng : factor R k k d=1 := mul_inv_cancel₀ nz
  have retr : finer r (le_refl k) y=y := by rw [base_value]; rfl
  dsimp only [E,state]
  rw [dif_pos (show k≤k ∧ k≤N from ⟨le_rfl,hk⟩),eng,one_smul]
  unfold moved WilsonThermometerOwnOffsetTale.strand
  rw [retr,filed]
  exact View.shift_at ..

variable {I : Type} [Fintype I] [DecidableEq I] (grades : I → ℕ)
variable (z : I → Site (R.family.side N p)) (y : (i:I) → Palette R.family (grades i))
  (V : (i:I) → Sight R.family (grades i) p) (r : (i:I) → Emblems R.family (grades i))
local notation "O" => WilsonThermometerOwnOffsetJoint.origins R z k
local notation "T" => (fun i=>R.family.localSection (grades i))
local notation "G0" => (fun _ : I=>(1:Signed))
local notation "F0" => (fun _ : I=>False)
local notation "Z0" => (fun _ : I=>(1:ℂ))
local notation "act" => (fun i=>state (k:=k) R (V i) (r i) (y i) (z i) k)

theorem original {t:ℕ} (hk:k<N)
    (H : ∀ i,Enrolled R.makes R.doors B k N p (grades i) (digits R N p (z i)) (V i) (r i))
    (row : WilsonThermometerIntrinsicRoster.filed R grades z y V r (Stock.census I) hk.le t) :
    ∃ (X : (i:I) → Coefficient (R.family.labels.level (grades i)) (R.family.side k p)),
      ∃ fmt : ∀ i,(X i).Format 0 R.family.params (P),
      (∀ i,Germ.projection (R.family.labels.level (grades i)) R.family.params (P).p.threshold 0 (X i)=
        (y i) (primaryLetter (grades i))) ∧
      (∀ i,(X i).remBound 0 (P) (kappa R.family.path k) (B (grades i) k*size (y i))) ∧
      ∃ (base : Neat (R.family.side k p) → Burst G (R.family.side k p) (P).p.threshold),
        IsoVac (P) base (R.family.path.levels.clock.forcedAllowance k) ∧
      ∃ (ι κ:Type),∃ (_:Fintype ι) (_:Fintype κ) (A:ι→SourceAt G (O)) (K:κ→Lifted G (O) (P).p.threshold),
        Unpacks A (P).p (fun _=>radius R t k k) (P).p.supportExponent 1 ∧
        Unfold (p:=(P).p) K (fun _=>radius R t k k) (P).p.supportExponent 1 ∧
        (∀ i,2≤(A i).fires.val.card) ∧ (∀ i,2≤(K i).fires.val.card) ∧
        WilsonThermometerIntrinsicRoster.density R grades z y r (Stock.census I) hk.le hk.le =
          credsX (O) (T) X fmt (G0) (F0) base (Z0) K A := by
  let w (_:I) := radius R t k k
  have positive (i:I) : 0<w i := radius_pos R t k k le_rfl
  choose X germ fmt price shift using fun i=>singleton R (z i) hk.le (y i) (H i)
  have place (i:I) : (O) i=site R hk.le (z i) := by
    change WilsonThermometerOwnOffsetNectar.location R (z i) k=_
    simp only [WilsonThermometerOwnOffsetNectar.location,dif_pos hk.le]
  have gate (i:I) : (act i).2.1=radiant (1:ℂ) (dye 1 False) ((O) i) ((X i).exponentialEntry 0 (T i) (P)) := by
    rw [place]
    simpa [radiant,dye,invoice] using (shift i).gate
  have lens (i:I) : profile (P).activities (act i).2.2 =
      sunny (P) (X i).forced (dye 1 False) ((O) i) (1:ℂ) := by
    rw [place]
    simpa [sunny,dye,invoice] using (shift i).lens
  have ht : (P).p=R.family.path.levels.budget k := (R.makes.wilson.represents N p k hk.le).vac
  have bill := (row k le_rfl hk.le).2.2
  rw [topPitch,if_neg hk.ne,←ht] at bill
  obtain ⟨U,Vv,cart,eps,hard,eq⟩ := bill
  obtain ⟨base,genuine⟩ := somebody (R.makes.wilson.represents N p k hk.le).good
  obtain ⟨ι,hI,L,hl,hot,sum⟩ := stokes (O) w U cart.exp eps positive
  obtain ⟨κ,hK,K,hk',hot',partners⟩ := knuckle (O) w Vv cart.flag hard positive
  refine ⟨X,fmt,germ,price,base,genuine,ι,κ,hI,hK,L,K,hl,hk',hot,hot',?_⟩
  have record := glintX (O) (T) X fmt (G0) (F0) base (Z0) (fun _=>by simp) U Vv K partners
    genuine L sum (fun j=>(cart.flag j).1)
  apply eq.trans
  rw [←record]
  congr 1
  · exact funext gate
  · exact funext lens

end YM.Integration.WilsonThermometerOwnOffsetWeakRows
end


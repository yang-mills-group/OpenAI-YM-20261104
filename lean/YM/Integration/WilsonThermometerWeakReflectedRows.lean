import YM.Integration.WilsonThermometerReflectedRoster
import YM.Integration.WilsonThermometerOwnOffsetWeakRows

/-! All copies of each weak field use one and the same filed primary, cost and hard
section before the true Wilson array is unpacked. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakReflectedRows
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open Next.Rank Edition Baler Value Glyph Thirst Alarm
open Trace.Physical Push.Local
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open WilsonThermometerOwnOffsetTale WilsonThermometerOwnOffsetNectar WilsonThermometerOwnOffsetRadii
open WilsonThermometerReflectedTrajectory
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {N p k d:ℕ}
local notation "P" => R.family.path.rep N p k
local notation "B" => WilsonThermometerOffsetLedger.cash R

theorem master {V:Sight R.family d p} {r:Emblems R.family d} (z:Site (R.family.side N p)) (hk:k≤N)
    (y:Palette R.family d) (H:Enrolled R.makes R.doors B k N p d (digits R N p z) V r):
    ∃ X:Coefficient (R.family.labels.level d) (R.family.side k p),
      X.Format 0 R.family.params (P) ∧ X.remBound 0 (P) (kappa R.family.path k) (B d k*size y) ∧
      Germ.projection (R.family.labels.level d) R.family.params (P).p.threshold 0 X=y (primaryLetter d) ∧
      V k y (line (primaryLetter d))=invoice X 0 (R.family.localSection d) (P) ∧
      ∀ (s:Motion) (c:Site (R.family.side k p)),View.Signpost (P) s (point R z s c k)
        (invoice X 0 (R.family.localSection d) (P)) (marked R z s c V r y k) := by
  let t:=primaryLetter d
  obtain ⟨u,hp⟩:=(H.legal k le_rfl hk).capacity0 y
  rcases hp with @⟨X,F,fee,b,tail,cert,wallet,assembled,hx,hy,financed⟩
  have spare:fee t≤B d k*size y:=((Finset.single_le_sum
    (fun j _=>rem_nonneg (wallet j)) (Finset.mem_univ t)).trans
    (le_add_of_nonneg_right tail.nonneg)).trans financed
  have filed:V k y (line t)=invoice (X t) 0 (R.family.localSection d) (P):=
    (congrArg (fun a:Tape G (R.family.side k p)=>a (line t)) assembled.symm).trans
      (together_line X F tail t)
  refine ⟨X t,cert t,rem_mono (wallet t) spare,(congrFun hy t).symm,filed,?_⟩
  intro s c
  have nz : (R.family.S.a k:ℂ)^d≠0:=pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (R.family.S.a_pos k).ne')
  have eng:factor R k k d=1:=mul_inv_cancel₀ nz
  have retr:finer r (le_refl k) y=y:=by rw [base_value];rfl
  unfold marked
  rw [dif_pos (show k≤k ∧ k≤N from ⟨le_rfl,hk⟩),eng,one_smul]
  unfold WilsonThermometerOwnOffsetTale.strand
  rw [retr,filed]
  exact View.spin_at ..

variable {J:Type} (d:J→ℕ) (z:J→Site (R.family.side N p)) (y:(j:J)→Palette R.family (d j))
  (V:(j:J)→Sight R.family (d j) p) (r:(j:J)→Emblems R.family (d j))
variable {I:Type} [Fintype I] [DecidableEq I]
local notation "Z0" => (fun _:I=>(1:ℂ))

theorem original (hk:k<N)
    (H:∀ j,Enrolled R.makes R.doors B k N p (d j) (digits R N p (z j)) (V j) (r j)):
    ∃ X:(j:J) → Coefficient (R.family.labels.level (d j)) (R.family.side k p),
      ∃ fmt:∀ j,(X j).Format 0 R.family.params (P),
      (∀ j,Germ.projection (R.family.labels.level (d j)) R.family.params (P).p.threshold 0 (X j)=
        y j (primaryLetter (d j))) ∧
      (∀ j,(X j).remBound 0 (P) (kappa R.family.path k) (B (d j) k*size (y j))) ∧
      (∀ j,V j k (y j) (line (primaryLetter (d j)))=invoice (X j) 0 (R.family.localSection (d j)) (P)) ∧
      ∀ (base:I→J) (s:I→Motion) (c:I→Site (R.family.side k p)) (t:ℕ),
        let D:=fun i=>d (base i)
        let Z:=fun i=>z (base i)
        let Y:=fun i=>y (base i)
        let vs:=fun i=>V (base i)
        let rs:=fun i=>r (base i)
        let O:=WilsonThermometerOwnOffsetJoint.origins R (fun i=>WilsonThermometerReflectedRoster.endpoint R (Z i) (s i) (c i)) k
        WilsonThermometerReflectedRoster.filed R D Z s c Y vs rs (Stock.census I) hk.le t →
        ∃ (vac:Neat (R.family.side k p)→ Burst G (R.family.side k p) (P).p.threshold),
          IsoVac (P) vac (R.family.path.levels.clock.forcedAllowance k) ∧
        ∃ (ι κ:Type),∃ (_:Fintype ι) (_:Fintype κ) (A:ι→SourceAt G O) (K:κ→Lifted G O (P).p.threshold),
          Unpacks A (P).p (fun _=>radius R t k k) (P).p.supportExponent 1 ∧
          Unfold (p:=(P).p) K (fun _=>radius R t k k) (P).p.supportExponent 1 ∧
          (∀ i,2≤(A i).fires.val.card) ∧ (∀ i,2≤(K i).fires.val.card) ∧
          WilsonThermometerReflectedRoster.density R D Z s c Y rs (Stock.census I) hk.le hk.le =
          credsX O (fun i=>R.family.localSection (D i)) (fun i=>X (base i)) (fun i=>fmt (base i))
            (fun i=>(s i).1) (fun i=>(s i).2) vac (Z0) K A := by
  choose X fmt price germ file shift using fun j=> master R (z j) hk.le (y j) (H j)
  refine ⟨X,fmt,germ,price,file,?_⟩
  intro base s c t D Z Y vs rs O row
  let w (_:I):=radius R t k k
  let act (i:I):=marked R (Z i) (s i) (c i) (vs i) (rs i) (Y i) k
  let T (i:I):=R.family.localSection (D i)
  let hand (i:I):=(s i).1
  let flip (i:I):Prop:=(s i).2
  have positive (i:I):0<w i:=radius_pos R t k k le_rfl
  have place (i:I):O i=point R (Z i) (s i) (c i) k:=
    WilsonThermometerReflectedRoster.parent R (Z i) (s i) (c i) le_rfl hk.le
  have gate (i:I):(act i).2.1=radiant (1:ℂ) (dye (hand i) (flip i)) (O i)
      ((X (base i)).exponentialEntry 0 (T i) (P)) := by
    rw [place];simpa [radiant,dye,invoice,hand,flip] using (shift (base i) (s i) (c i)).gate
  have lens (i:I):profile (P).activities (act i).2.2=
      sunny (P) (X (base i)).forced (dye (hand i) (flip i)) (O i) (1:ℂ) := by
    rw [place];simpa [sunny,dye,invoice,hand,flip] using (shift (base i) (s i) (c i)).lens
  have ht:(P).p=R.family.path.levels.budget k := (R.makes.wilson.represents N p k hk.le).vac
  have bill:=(row k le_rfl hk.le).2.2
  rw [topPitch,if_neg hk.ne,←ht] at bill
  obtain ⟨U,Vv,cart,eps,hard,eq⟩:=bill
  obtain ⟨vac,genuine⟩:=somebody (R.makes.wilson.represents N p k hk.le).good
  obtain ⟨ι,hI,L,hl,hot,sum⟩:=stokes O w U cart.exp eps positive
  obtain ⟨κ,hK,K,hk',hot',partners⟩:=knuckle O w Vv cart.flag hard positive
  refine ⟨vac,genuine,ι,κ,hI,hK,L,K,hl,hk',hot,hot',?_⟩
  have record:=glintX O T (fun i=>X (base i)) (fun i=>fmt (base i)) hand flip vac (Z0) (fun _=>by simp)
    U Vv K partners genuine L sum (fun j=>(cart.flag j).1)
  apply eq.trans
  rw [←record];congr 1
  · exact funext gate
  · exact funext lens

end YM.Integration.WilsonThermometerWeakReflectedRows
end

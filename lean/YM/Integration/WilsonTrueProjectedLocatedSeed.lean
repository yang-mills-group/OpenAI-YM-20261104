import YM.Integration.WilsonTrueProjectedLocatedInitial
import YM.Integration.WilsonOriginalNullColumnSplit
/-! The genuine aligned comparison with an independently printed rough
ultraviolet seed. Its measured coordinate is read at the landing. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedLocatedSeed
open Filter MeasureTheory Lattice RG Wilson Extra.Histories Source Labels
open Extra.Histories.Relay Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open QuadraticLocal QuadraticLocal.Advent AllOrder AllOrder.Floe AllOrder.Transit WheelP WilsonOriginalNullCorridor
open scoped Classical Topology BigOperators

open FormalBulk08 City Pose RemainderComparison ConnectedActivityE6
open WilsonTrueProjectedPointProgram WilsonTrueProjectedPointInverse
open WilsonTrueProjectedLocatedBasis WilsonTrueProjectedLocatedHistory
open WilsonPinnedWidthTransport WilsonTrueProjectedNaturalFee WilsonTrueProjectedCourse
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G)
local notation "C₀" => R.family


open WilsonTrueProjectedLocatedFunded WilsonTrueProjectedLocatedMerge


open WilsonTrueProjectedLocatedOrigin
variable {d N p b n : ℕ} {W : ∀ i,Rep G ((C₀).side i p)} {o : ∀ i,Site ((C₀).side i p)}
local notation "L" => (C₀).labels.level d
local notation "S" => (C₀).localSection d
local notation "P" => (C₀).path.rep N p
local notation "τ" => safety (C₀)


open Push.Local Extra.Histories.Relay
theorem subtract {d₀ : ℕ} {F₀:Frame G d₀} {A:Hol G} {n₀:Side} {W:Rep G n₀} {o:Site n₀}
    {S₀:SectionData F₀} {a c f t s:ℝ} (law:W.Lawful a c f t s) (d₁:d₀≤W.p.order) (d₂:d₀≤W.p.power)
    (h k:Coefficient F₀ n₀) {κ u v:ℝ} (hf:h.Format o A W) (hp:h.remBound o W κ u)
    (kf:k.Format o A W) (kp:k.remBound o W κ v) (hz:projection F₀ A W.p.threshold o h=0)
    (kz:projection F₀ A W.p.threshold o k=0) :
    ∃ H:Coefficient F₀ n₀,H.Format o A W ∧ H.remBound o W κ (u+v) ∧ projection F₀ A W.p.threshold o H=0 ∧
      H.density o S₀ W=h.density o S₀ W-k.density o S₀ W := by
  let m:=stretch (-1:ℂ) k
  have fmt:m.Format o A W:=stretch_format (-1:ℂ) kf
  have rent:m.remBound o W κ v:=by simpa only [norm_neg,norm_one,one_mul] using stretch_rem (-1:ℂ) kp
  have joint:=presentation hf hp fmt rent
  refine ⟨beside h m,joint.1,joint.2,?_,?_⟩
  · rw [add_projection d₀ h m hf fmt d₁ d₂ ⟨_,_,hp⟩ ⟨_,_,rent⟩,hz,zero_add]
    change projection F₀ A W.p.threshold o (stretch (-1:ℂ) k)=0
    rw [WilsonOriginalNullColumnSplit.scale_page A W o k (-1) d₁ d₂ kf kp,kz,smul_zero]
  · rw [plus law hp rent S₀];funext U
    change h.density o S₀ W U+(stretch (-1:ℂ) k).density o S₀ W U=_
    rw [stretch_density];simp [sub_eq_add_neg]

theorem original {W : ∀ i,Rep G ((C₀).side i p)} {o : ∀ i,Site ((C₀).side i p)}
    {F : ∀ j,Config G ((C₀).side (b+j) p) → ℂ} {price : ℕ → ℝ} {ε total : ℝ}
    (H : Receipt R d N p b n W o F price ε)
    (paid : (∑ j : Fin n,(H.u j+H.e j)) ≤ total) (live : b+n≤N) (ep:0≤ε)
    (grid : ∀ i≤n,o (b+i)=((C₀).S.toDepth (show b≤b+i by omega) p).embed (o b))
    (route : ∀ j<n,o (b+j)=((C₀).path.levels.clock.op (b+j) p).ratio.parent (o (b+j+1)))
    (laws : ∀ j≤n,∃ a c f t s:ℝ,(W (b+j)).Lawful a c f t s) (houses : ∀ j≤n,Opened C₀ d (b+j) p)
    (gates : ∀ j<n,WilsonOriginalNullPlacedParallel.Joined C₀ d N p (b+j) W (o (b+j+1)) ε)
    (same : ∀ j≤n,(W (b+j)).p=(P (b+j)).p) (quiet : ∀ j≤n,∀ U,(W (b+j)).eval U=(P (b+j)).eval U)
    (v : (C₀).label d) (h k : store C₀ d p (b+n)) {B D:ℝ}
    (hf:h.Format (o (b+n)) (C₀).params (W (b+n))) (hp:h.remBound (o (b+n)) (W (b+n)) (τ (b+n)) B)
    (kf:k.Format (o (b+n)) (C₀).params (P (b+n))) (kp:k.remBound (o (b+n)) (P (b+n)) (τ (b+n)) D)
    (null : projection L (C₀).params (W (b+n)).p.threshold (o (b+n)) h+
      projection L (C₀).params (P (b+n)).p.threshold (o (b+n)) k=0)
    (top : F n=placed R d N p b o n v+
      (h.density (o (b+n)) S (W (b+n))+k.density (o (b+n)) S (P (b+n)))) (inc : Integrable (F n) (prior G _))
    (y : store C₀ d p b) (a : ℝ) (yf:y.Format (o b) (C₀).params (W b))
    (yp:y.remBound (o b) (W b) (τ b) a) (file:y.density (o b) S (W b)=F 0) :
    let home:Opened C₀ d b p:=houses 0 (Nat.zero_le _)
    let x:=(fitting (C:=C₀) d N p b R.makes home (by omega)).symm (projection L (C₀).params (W b).p.threshold (o b) y)
    ∃ (z q:store C₀ d p b) (u e:ℝ),
      z.Format (o b) (C₀).params (W b) ∧ z.remBound (o b) (W b) (τ b) u ∧
      projection L (C₀).params (W b).p.threshold (o b) z=0 ∧ q.Format (o b) (C₀).params (P b) ∧
      q.remBound (o b) (P b) (τ b) e ∧ projection L (C₀).params (P b).p.threshold (o b) q=0 ∧
      u+e≤total+gain C₀ b (b+n)*(B+D) ∧
      placed R d N p b o 0 x=F 0+z.density (o b) S (W b)+q.density (o b) S (P b) := by
  classical
  intro home x
  let J:=image R o home (show b≤N by omega)
  obtain ⟨a₀,c₀,f₀,t₀,s₀,law⟩:=laws 0 (Nat.zero_le _)
  have native:(W b).p=(P b).p:=same 0 (Nat.zero_le _)
  have state:∀U,(W b).eval U=(P b).eval U:=quiet 0 (Nat.zero_le _)
  have dims:=dimensions d N p b R.makes home.post (show b≤N by omega)
  have dw:d≤(W b).p.order:=native ▸ dims.1
  have pw:d≤(W b).p.power:=native ▸ dims.2
  obtain ⟨z,q,zf,qf,zp,qp,zn,qn,_,_,bill,field⟩:=WilsonTrueProjectedLocatedBalance.original R H paid (by omega) home law dw pw
  obtain ⟨v₀,w₀,ret,u,e,vf,vp,vz,wf,wp,wz,due,earlier⟩:=WilsonTrueProjectedLocatedInitial.original
    R live home grid route (fun j hj=>laws j hj.le) (fun j hj=>houses j hj.le) ep gates (same n le_rfl)
      (quiet n le_rfl) h k hf hp kf kp null
  let boot:=h.density (o (b+n)) S (W (b+n))+k.density (o (b+n)) S (P (b+n))
  have source:Integrable (placed R d N p b o n v) (prior G _):=
    WilsonOriginalNullPlacedLinearPanel.tested R d live (houses n le_rfl) (o (b+n)) v
  have cancel:Integrable boot (prior G _):=by
    have dif:F n-placed R d N p b o n v=boot:=by rw [top];dsimp [boot];abel
    exact dif ▸ (inc.sub source)
  have left:flow C₀ d N p b n (F n)=J v+(v₀.density (o b) S (W b)+w₀.density (o b) S (P b)+J ret):=by
    rw [top,flow_add R.family d N p b n _ _ source cancel,WilsonTrueProjectedLocatedInitial.aligned R live home grid n le_rfl,earlier];rfl
  let feeds:=∑j:Fin n,∑i∈Finset.range j.val,H.feed j i
  let heads:=∑j:Fin n,H.primary j
  have fstep:(∑j:Fin n,∑i∈Finset.range j.val,flow C₀ d N p b i (placed R d N p b o i (H.feed j i)))=J feeds:=by
    simp only [feeds,map_sum];apply Finset.sum_congr rfl;intro j _
    apply Finset.sum_congr rfl;intro i hi
    exact WilsonTrueProjectedLocatedInitial.aligned R live home grid i ((Finset.mem_range.mp hi).le.trans j.isLt.le) _
  have pstep:(∑j:Fin n,flow C₀ d N p b j (placed R d N p b o j (H.primary j)))=J heads:=by
    simp only [heads,map_sum];exact Finset.sum_congr rfl (fun j _=>WilsonTrueProjectedLocatedInitial.aligned R live home grid j j.isLt.le _)
  rw [fstep,pstep,left] at field
  obtain ⟨z₀,ff,fp,fn,fc⟩:=subtract (S₀:=S) law dw pw z v₀ zf zp vf vp zn vz
  obtain ⟨q₀,gf,gp,gn,gc⟩:=subtract (S₀:=S) (R.makes.wilson.represents N p b (by omega)).good dims.1 dims.2 q w₀ qf qp wf wp qn wz
  let x₀:=v+ret-feeds-heads
  let start:Config G (R.family.side b p)→ℂ:=F 0
  let soft:Config G (R.family.side b p)→ℂ:=z₀.density (o b) S (W b)
  let canonical:Config G (R.family.side b p)→ℂ:=q₀.density (o b) S (P b)
  let Z:Config G (R.family.side b p)→ℂ:=z.density (o b) S (W b)
  let Q₀:Config G (R.family.side b p)→ℂ:=q.density (o b) S (P b)
  let V:Config G (R.family.side b p)→ℂ:=v₀.density (o b) S (W b)
  let W₀:Config G (R.family.side b p)→ℂ:=w₀.density (o b) S (P b)
  have sc:soft=Z-V:=fc
  have cc:canonical=Q₀-W₀:=gc
  have full:J v+(V+W₀+J ret)=start+Z+Q₀+J feeds+J heads:=field
  have totalField:J x₀=start+soft+canonical:=by
    dsimp only [x₀];rw [map_sub,map_sub,map_add,sc,cc]
    calc
      _ = (J v+(V+W₀+J ret))-V-W₀-J feeds-J heads := by abel
      _ = _ := by rw [full];abel
  have fitted:J x₀=(y.density (o b) S (W b):Config G (R.family.side b p)→ℂ)+soft+canonical :=
    totalField.trans (congrArg (fun f:Config G (R.family.side b p)→ℂ=>f+soft+canonical) file.symm)
  have coord:=WilsonTrueProjectedLocatedPage.read R (show b≤N by omega) home (o b) (W b) native state law x₀ y z₀ q₀ a _ _
    yf yp ff fp gf gp fn gn fitted
  let φ:=fitting (C:=C₀) d N p b R.makes home (show b≤N by omega)
  have equal:x=x₀:=(congrArg φ.symm coord.symm).trans (φ.symm_apply_apply _)
  refine ⟨z₀,q₀,_,_,ff,fp,fn,gf,gp,gn,by linarith only [bill,due],?_⟩
  rw [equal];exact totalField

end YM.Integration.WilsonTrueProjectedLocatedSeed

import YM.Integration.WilsonIndependentMatchedFiniteFees

/-! The actual stopped mixed comparison on the elected finite collar,
written entirely in terms of homogeneous coefficients of placed group
stencils on finite tori and the unmarked finite history. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentMatchedFiledRosterStop
open Filter Function Matrix Lattice RG Laurent Bloch Metric FreeResolvent Work.F08
open Wilson Tree Precision AnalyticNext.QuarticMatch.Sheets Exterior Next.Free
open Gauge Source Labels XSpace PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Soil WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Shard WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Blue WilsonCoeffUV.Embroider WilsonCoeffUV.Power WilsonCoeffUV.StableStrip
open PertExtension RegulatorIR
open WilsonIndependentMatchedElectedFaces (Sheet Slot mounted)
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentMatchedFiledIncome (plate)
open WilsonIndependentMatchedCoverProfile (word)
open WilsonIndependentMatchedFittedSeat (receiving)
open WilsonIndependentMatchedCensusReceipt (Filed)
open WilsonIndependentMatchedRosterPlanted (response)
open scoped Classical BigOperators Topology

variable {G:Gauge}{H:Hol G}{n h D k e u₀:ℕ}{p:h<D}{v:Rails h k u₀ e}{E W₁ K U:Credit}
  (P:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)(M:Master H)
  (X:Fin (n+1)→CutsP H (M.T h) p v E W₁ K U)(kind:Fin (n+1)→Bool)(d:Fin (n+1)→ℕ)
  (w:∀i,d i<D)(c:(i:Fin (n+1))→Verse (P.family.labels.level (d i)))
  (a amp:Fin (n+1)→ℝ)(φ:Fin (n+1)→Rarity D)(y:ℝ)(o:CellR)

def mesh (i:Fin (n+1)):=paceT (X i).ax.S (X i).m ((X i).m+(X i).i)
def sources (b:Side):Ink (Woods G b):=
  ∏i,WilsonIndependentMatchedOrdinaryProfile.stems P W b (kind i) (w i) (a i • c i) (φ i) (mesh M X i) y o h
def pivots (b:Side):Ink (Woods G b):=
  ∏i,WilsonIndependentMatchedElectedSection.profile (M.T h) p b ((a i/amp i) • (X i).tileP) (φ i) (mesh M X i) y o h
def returned (stop:ℕ)(film:(b:Side)→Ink (Woods G b))(b:Side)(j:ℕ)(t:Fin 0→YForest G):ℝ:=
  WilsonIndependentConditionalMarkedCover.tensor (WilsonIndependentMatchedOrdinaryHistory.scalar
    (X 0).ax (X 0).tx (X 0).N ((n+1)*k-1) ((X 0).m+(X 0).i) stop film b) j 0 (slideC b t)

theorem original (L:Torch H (M.T h) p v E W₁ K)(run:XSpace.Run)(base idx start:ℕ)
    (δ η:ℝ)(fees:Fin (n+1)→ℝ)
    (books:∀i,Filed (X i) L run base idx start (amp i) δ η (fees i)
      (Shrine (plate (sectionAt P W (kind i) (d i)) (w i)) (c i)))
    (level:∀i,d i≤k)(nonempty:0<k)(stop u:ℕ)(before:stop≤(X 0).m+(X 0).i)
    (C:ℝ)(sale:response e u (
      cruises (X 0).ax (X 0).tx (X 0).N ((n+1)*k) ((X 0).m+(X 0).i) stop
        (MassP G ℝ n (fun i=>word (a i • Shrine (plate (sectionAt P W (kind i) (d i)) (w i)) (c i))
          (φ i) (mesh M X i) y o h))-
      cruises (X 0).ax (X 0).tx (X 0).N ((n+1)*k) ((X 0).m+(X 0).i) stop
        (MassP G ℝ n (fun i=>receiving (X i) (a i/amp i) (φ i) y o (X i).i))) C)
    (j:ℕ)(order:j≤e)(t:Fin 0→YForest G)(ε:ℝ)(extra:0<ε):
    ∀ᶠ b in atTop,
      ‖returned M X stop (sources P W M X kind d w c a φ y o) b j t-
        returned M X stop (pivots M X a amp φ y o) b j t‖≤C+ε:=by
  let T (i:Fin (n+1))(mode:WilsonIndependentMatchedElectedFaces.Slot):Sheet G:=mounted P W M (X i) L run base idx start (amp i) δ η (fees i)
    (c i) (books i) (a i) (φ i) y o mode
  have high:(n+1)*k-1+1=(n+1)*k:=Nat.sub_add_cancel (Nat.mul_pos (Nat.succ_pos n) nonempty)
  have th:(X 0).m+(X 0).i≤(X 0).N:=(X 0).hc.trans (X 0).hn
  have cap₁:(∑i,(T i .full).grade)≤(n+1)*k-1+1:=by
    rw [high]
    change (∑i,d i)≤(n+1)*k
    simpa using Finset.sum_le_sum (s:=Finset.univ) (fun i _=>level i)
  have cap₂:(∑i,(T i .fitted).grade)≤(n+1)*k-1+1:=by
    rw [high]
    change (∑_i:Fin (n+1),h)≤(n+1)*k
    simpa using Nat.mul_le_mul_left (n+1) v.hk
  have planted (i:Fin (n+1)):(T i .full).field=word (a i • Shrine (plate (sectionAt P W (kind i) (d i)) (w i)) (c i))
      (φ i) (mesh M X i) y o h:=by
    change word ((a i/amp i) • (X i).pt) (φ i) (mesh M X i) y o h=_
    rw [(books i).actual]
  have observed (i:Fin (n+1)):(T i .fitted).field=receiving (X i) (a i/amp i) (φ i) y o (X i).i:=rfl
  apply WilsonIndependentMatchedFiniteFees.paid (X 0).ax (X 0).vesselsC.hG (X 0).vesselsC.green before th
    (fun i=>T i .full) (fun i=>T i .fitted) cap₁ cap₂ (e:=e) (u:=u) (C:=C) _ j order t ε extra
  simpa only [high,planted,observed] using sale

end YM.Integration.WilsonIndependentMatchedFiledRosterStop

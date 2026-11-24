import YM.Integration.WilsonIndependentMatchedCoverCrossing
import YM.WilsonCoeffUV.Product.I.Ripple

/-! A newly formed two-source field is passed through the full remaining
normalized interval on the actual cover. Rank zero is read on that same output. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedCoverJoined
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical
variable {G:Gauge}{D D' k l r e u b:ℕ}{E W L:Credit}

lemma unit {V:Era G ℝ}{A η:ℝ}(paid:Flush e u η V A)(j:ℕ)(hj:j≤e)
    (x:Fin 0→YForest G):‖V.2 j 0 x‖≤A:=by
  have h:=paid.2 j hj 0 (Nat.zero_le _)
  have one:hedge 0 η u x * ‖V.2 j 0 x‖≤A:=(h.2.1.le_tsum x (fun t _=>h.1 t)).trans h.2.2
  rw [autumn_empty G η 0 u x] at one
  simpa only [hedge,autumn,zero_mul,add_zero,one_pow,one_mul] using one

theorem original (G:Gauge)(l r k e u b:ℕ)(E W L:Credit):
    ∃ C:Credit,∀(R:Realm G (e+1) E)(_sale:SpringD R k u b W)
      (_older:Dormitory R (l+r) u L)(m i c N:ℕ)(_live:R.anchor ≤ i)(_earlier:i<c)
      (_above:c≤N)(_room:l+r≤k)(η:ℕ→ℝ)(Z:ℝ)(_escort:Escort R m i η)
      (_cash:PadRank R m i Z)
      (φ:Rarity D)(ψ:Rarity D')(P Q:Era G ℝ)(x y t z:ℝ)(o:CellR)
      (_mesh:0<x)(_fit:x*(ll R.draws i).L.val≤1)(_spacing:η i=x*(ll R.draws i).L.val)
      (_sep:ClearDay φ ψ t)(_pos:0<t)
      (_pfit:radiusH φ (x*(ll R.draws i).L.val) y≤z)
      (_qfit:radiusH ψ (x*(ll R.draws i).L.val) y≤z)
      (_lp:(VisitsT φ x y o).Nonempty)(_rp:(VisitsT ψ x y o).Nonempty)(A B:ℝ)
      (_left:Income P l e (u+b) (OrbP (ll R.draws i) φ x y o) A)
      (_right:Income Q r e (u+b) (OrbP (ll R.draws i) ψ x y o) B),
    let born:=JoinGap R.draws R.paid i N l r P Q
    let reached:=cruises R.draws R.paid N (l+r) i m born
    let fee:=C.buy Z*(R.cash (priceWG G e k u b E W) i*(pearlB u b (4*z) (t/(η i))*(A*B)))
    verseI R.draws R.paid i N (l+r) (agateV P Q)=
        born+agateV (verseI R.draws R.paid i N l P) (verseI R.draws R.paid i N r Q) ∧
    Flush e u (η m) reached fee ∧ ∀j≤e,∀q:Fin 0→YForest G,‖reached.2 j 0 q‖≤fee :=by
  obtain ⟨C,later⟩:=waveSeen G (l+r) e u E L
  refine ⟨C,?_⟩
  intro R sale older m i c N live earlier above room η Z escort cash φ ψ P Q x y t z o mesh fit
    spacing sep hsep pfit qfit lp rp A B left right
  dsimp only
  obtain ⟨step,paid⟩:=WilsonIndependentMatchedCoverCrossing.original R sale live earlier above
    room P Q x y t z o mesh fit sep hsep pfit qfit lp rp left right
  rw [←spacing] at paid
  have fine:=earlier.trans_le above
  have admitted:Auth (l+r) (JoinGap R.draws R.paid i N l r P Q):=
    (Auth.verse R.draws fine R.hG R.green (left.1.manor right.1)).sub
      ((Auth.verse R.draws fine R.hG R.green left.1).manor (Auth.verse R.draws fine R.hG R.green right.1))
  let δ:=max (0:ℝ) (R.tempC i i)
  have received:=(later R older m i η i N N _ δ Z escort cash le_rfl fine.le fine.le
    (le_max_right _ _) _ _ (Fringed.same paid admitted (le_max_left _ _))).f_l
  exact ⟨step,received,fun j hj=>unit received j hj⟩

end YM.Integration.WilsonIndependentMatchedCoverJoined

import YM.Integration.WilsonIndependentConditionalPulledCover
import YM.Integration.WilsonIndependentMatchedOrdinaryReceiver

/-! Re-evaluate an actual finite history from the deposited polynomial.
At each age use its full old unmarked story, normalized heat, conditional
mean and measured kinetic redo. No additional field election occurs. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentMatchedOrdinaryHistory
open Lattice RG WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Bank WilsonCoeffUV.Cosmos WilsonCoeffUV.Soil
open WilsonCoeffUV.Shard FreeResolvent RegulatorIR RegulatorIR.Ledger RegulatorIR.Oracle
open Laurent Bloch Exterior Stationary Work.F08 Matrix Metric Precision Next.Free Tree
open WilsonCoeffUV.Blue Embroider Embroider.Canvas PowerSeries RegulatorIR.Diagram
open WilsonCoeffUV.Convention
open scoped Classical BigOperators
variable {G:Gauge}

/-- The finite conditional on the supplied full homogeneous tensors. -/
def step (A:Levels G)(Ñ:ChartRatio G)(m N k:ℕ)(c:Side)(P:Ink (Woods G (c*(loose A m).L))):Ink (Woods G c):=
  let S:=mStep A c m;let F:=repeatF S;let H:=freeForms A N (m+1);let Q:=roam A N m c
  let V:=(story A Ñ N (m+1)).1 (c*(loose A m).L)
  redo (ratioHigh A Ñ N m) (rated (fun e=>e+(k+1)) (WilsonIndependentConditionalPulledBoard.output S F H Q Ñ V
    (WilsonIndependentConditionalMarkedCover.tensor P) (k+1)))

theorem filed (A:Levels G){Ñ:ChartRatio G}(simple:G.Simple)(ratio:LocalRatio Ñ)
    {m N k:ℕ}(finer:m<N)(c:Side)(Z:Era G ℝ)(auth:Auth (k+1) Z):
    step A Ñ m N k c (flash (Z.1 (c*(loose A m).L)))=flash ((verseI A Ñ m N (k+1) Z).1 c):=by
  have keep:WilsonIndependentConditionalMarkedCover.tensor (flash (Z.1 (c*(loose A m).L)))=Z.1 (c*(loose A m).L):=by
    funext j r;exact WilsonIndependentConditionalMarkedCover.reads (auth.span _) (auth.pale _) j r
  unfold step
  rw [keep]
  exact WilsonIndependentConditionalPulledCover.received A simple ratio finer c Z auth

/-- The entire finite torus computation, specified solely by its top
polynomial and the common unmarked prior on each successive board. -/
def scalar (A:Levels G)(Ñ:ChartRatio G)(N k top m:ℕ)(source:(n:Side)→Ink (Woods G n))(c:Side):Ink (Woods G c):=
  if m<top then step A Ñ m N k c (scalar A Ñ N k top (m+1) source (c*(loose A m).L)) else source c
termination_by top-m

theorem cleared (A:Levels G){Ñ:ChartRatio G}(simple:G.Simple)(ratio:LocalRatio Ñ)
    {m N k top:ℕ}(lower:m≤top)(finer:top≤N)(Z:Era G ℝ)(auth:Auth (k+1) Z)
    (source:(n:Side)→Ink (Woods G n))(intake:∀c,flash (Z.1 c)=source c)(c:Side):
    scalar A Ñ N k top m source c=flash ((cruises A Ñ N (k+1) top m Z).1 c):=by
  induction lower using Nat.decreasingInduction generalizing c with
  | self=>rw [scalar,if_neg (Nat.lt_irrefl _),cruises_top,intake]
  | of_succ i hi ih=>
    rw [scalar,if_pos hi,ih,cruises_sub A Ñ N (k+1) Z hi]
    exact filed A simple ratio (hi.trans_le finer) c _ (cruising A simple ratio hi finer auth)

theorem covered (A:Levels G){Ñ:ChartRatio G}(simple:G.Simple)(ratio:LocalRatio Ñ)
    {m N k top:ℕ}(lower:m≤top)(finer:top≤N)(Z:Era G ℝ)(auth:Auth (k+1) Z)
    (source:(n:Side)→Ink (Woods G n))(intake:∀c,flash (Z.1 c)=source c)(j r:ℕ):
    Bends 0 (fun c=>WilsonIndependentConditionalMarkedCover.tensor (scalar A Ñ N k top m source c) j r)
      ((cruises A Ñ N (k+1) top m Z).2 j r):=by
  have h:=cruising A simple ratio lower finer auth
  simpa only [cleared A simple ratio lower finer Z auth source intake,
    WilsonIndependentConditionalMarkedCover.reads (h.span _) (h.pale _)] using h.wing j r

end YM.Integration.WilsonIndependentMatchedOrdinaryHistory

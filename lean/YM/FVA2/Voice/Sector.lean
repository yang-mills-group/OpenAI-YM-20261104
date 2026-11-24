import YM.FVA2.Continuum.Reg
import YM.FVA2.Arrival.Episodes
/-!
# Raw (before W-compensation) columns of the operator prescription

Does one have **exact** identities even starting from the multiscale form of the
prescription? `Core.first` answers this for the starting raw column and the `ApplyM`
fee formulation. See `Voice/Encore.lean` to go further, connect also the W-compensated
rows and apply both literal MS endpoints.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Voice
open Function Filter Set Finset MeasureTheory Lattice Wilson
open Maxwell Maxwell.Free
open MS MS.Book MS.Book.Convolve MS.Book.Program MS.Plane MS.Koszul MS.Native MS.Wind MS.Rake MS.Theater MS.Menus MS.Tide MS.Fleet MS.Momentum
open MS.Orbit MS.Swirl MS.Swirl.Near MS.High MS.Vista MS.Land
open Arrival Arrival.Episodic Change Slice Press XPos
open PertExtension FormalOPE.RG10 FormalOPE.RG10.MultiGauge Splice
open scoped Classical Topology BigOperators ContDiff
variable {W:Type}{G:Gauge}(Y:XSpace.Initialize G)
namespace Core
-- attach unconstrained pure `inl` token to get only the raw leading column in the same horizon
abbrev tag (x:Birth G): Folio G:= Birth.chooses x ( Sum.inl () )
variable (x:Birth G)
lemma at_pure : Glyph.hand (Press.wickInput Y) x.glyph ( Sum.inl () ) =(Press.program Y).stamp x.glyph.size x.glyph.grade x.glyph.2.2:= rfl
lemma is_entry : Folio.entry Y ( tag x )=Glyph.lit (Press.program Y) x.glyph:= rfl
lemma origin (n:Lattice.Side) : Folio.placard Y ( tag x ) n= (( dictionary Y ).node x.glyph).placed n x.at':= rfl -- definitional
lemma owns : Folio.asset [tag x]= x.glyph.grade:= by rfl
-- hence exact finite Wilson estimator on these coeffs, not requiring ANY MS choices.
variable (u: W→ Label ( Press.portDeck G )) (L:Cover)(d:W→Cover)(n:Lattice.Side)
abbrev put (l:List (Dictionary.vertices u)): List (Folio G):= l.map (tag ∘ Top.declares u L d)
lemma amount (l) : ( dictionary Y ).raw u L d n l = Folio.coefficients Y n (put u L d l):= by rw [Dictionary.raw,Folio.coefficients,Folio.asset,Change.joints, Folio.scenario,Change.joints, put,List.map_map,List.map_map]; rfl
-- Take an epoch reading and reassemble the full MS source combinations.
variable {n} (E:Hearth.Epoch G n) {J: Precision.ChartRatio G} (H:Precision.LocalRatio J)
variable (M:Land.Prescription (Press.portDeck G))(a:ℝ) [LinearOrder W](s:Finset W)
def through : MS.Book.Convolve.T ℂ:= Change.convertSources (Dictionary.paid u M a) s.toList (fun l=> substitute (Program.shift M.team a) (Slice.record (Episodic.candle Y E H (put u L d l))))
omit [LinearOrder W] in
lemma deserving : through Y u L d E H M a s=( Press.dictionary Y ).finite u L d s M n a:= by unfold through Dictionary.finite; simp_rw [Episodic.candle_eq,amount]
-- To compare also for the W-shifted columns use `ApplyMF`, via `Ticket.total`.
lemma first : PhysicalSum G M.team a n true s d L ( ApplyM (Press.program Y) (Stripped M.team) M u ) ( through Y u L d E H M a s ):= by rw [ deserving ]; exact (( Press.dictionary Y ).identify u n L d E.F.even s M a).2 rfl
end Core
end YM.FVA2.Voice

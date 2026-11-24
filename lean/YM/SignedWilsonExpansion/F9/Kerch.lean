import YM.SignedWilsonExpansion.F9.Colic
/-!
# Port matrix payment from at-Front independent accounts
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 580000
namespace YM.SignedWilsonExpansion.Commission.Method
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open FVA2 FVA2.Arrival FVA2.Main FVA2.Scale FVA2.Position FVA2.Position.Axes Jury Reg
open scoped Topology ContDiff BigOperators Classical
open WilsonCoeffUV.Mer.Xa
open Stair Tape RateQ
variable {G:Gauge}{n d k e j l:ℕ} {ι:Type} {L:Filter ι}{q:ι→ℝ}
variable (h:G.Simple)(T:MS_Data G (Position.OpenAxis.Plot (FVA2.Press.portDeck G)))(S:Prescription ( FVA2.Press.portDeck G)) (W:Initialize G){P':Normalize.Store G}(K:Rose.Pick P') (M:Scale.System.Contract W K T S)
variable {X:Type*} [NormedField X]
variable (Y:Initialize G) (V: Normalize.Store G) 
section modules
variable (t:ι→Mesh) (x:Maxer L q)(p:Expense.Stretched L t)
variable {E F L':Type}[AddCommGroup E][Module ℂ E][AddCommGroup F][Module ℂ F][AddCommGroup L'][Module ℂ L']
variable {C:Normalize.Guard G d}
include x
lemma rotate_b [FiniteDimensional ℂ E][FiniteDimensional ℂ F] {U:ι→ E→ₗ[ℂ] F}{Y:ι→ F→ₗ[ℂ]L'} (u:Across L q ℂ U)(v:Across L q ℂ Y): Across L q ℂ (fun i=> Y i ∘ₗ U i):=by
    apply Across.actEnough x (Module.finBasis ℂ E); intro i; change Across L q ℂ (fun j=> Y j (U j ((Module.finBasis ℂ E) i))); exact Across.linearAt x v (E:=F) (Across.linearAt x u (Across.solid ((Module.finBasis ℂ E) i))) -- needs orientation order?
lemma power_b [FiniteDimensional ℂ E] (U:ι→ Module.End ℂ E)(u:Across L q ℂ U)(i:ℕ): Across L q ℂ (fun v=> (U v)^i):=by
    induction i with
    | zero=>simp_rw [pow_zero]; exact Across.solid _
    | succ i ih=> simp_rw [pow_succ]; exact rotate_b x u ih
lemma booth_b (T:ι→ Labels.Label G d→ₗ[ℂ] Sec G d)(u:Across L q ℂ T): Across L q ℂ (fun i=> booth (T i)):=by
   apply Across.sum (P:=fun i j=> upsTurn ( T i )^j) x; exact fun j _=> power_b x _ (Across.acrossSub x (Across.solid (1:Module.End ℂ (Sec G d))) (rotate_b x (Across.solid (ladderS d)) u)) j
include p
lemma changeFee : Across L q ℂ (fun i=> coeff 0 (deck (V.layout Y (t i) d))):=by
    let f i:= V.layout Y (t i) d 0; let B:=Module.finBasis ℝ (Change G d); have ht:Across L q ℝ f:=by
       apply Across.basisN x B; obtain hv:= (V.nested_solution Y d p).1.trans_tendsto p.endpt; simp only [sub_zero,Pi.zero_apply] at hv; exact Billed.tens hv
    letI : FiniteDimensional ℝ (Module.End ℂ (Sec G d)):= Module.Finite.trans ℂ _; simp_rw [coeff_zero_eq_constantCoeff_apply,const_deck]; exact Across.acrossAdd x (Across.solid (1:Module.End ℂ (Sec G d))) ( Across.realComplex x (P:=fun i=>(f i).val) (by let L': (Change G d) →ₗ[ℝ] Module.End ℂ (Sec G d) := (Change G d).subtype; exact Across.arrow (F:=Module.End ℂ (Sec G d)) ht L') )
end modules
open Lattice
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Mer
open Wilson Gauge WardBin -- kernel names
variable {E:WilsonCoeffUV.Bank.Credit}
structure Epic (W:Initialize G)(F:Labels.Frames G)(K:∀ h,Rays G h W.hol)(Ω:Council F)(R:Realm G (e+1) E) (d k v:ℕ) where
     m:ℕ
     c:ℕ
     l:ℕ
     mesh:Mesh
     ρ:ℝ
     Z:ℝ
     paid : Stair Ω (launch F W.hol W.surveys K k) R.draws R.paid m c c d e k v Z
     align : mesh.spacing=sizeT R.draws ρ c
-- `v` price parameter. theta over filters.
namespace Epic
variable {v:ℕ}{K':∀ h,Rays G h W.hol}{F:Labels.Frames G}{Ω:Council F}{R:Realm G (e+1) E} (q':ι→ Epic W F K' Ω R d k v)
-- bureaucratic pointer can survive layers
abbrev tenor (X: Epic W F K' Ω R d k v):= X.paid.publish W X.mesh X.ρ V X.l
abbrev voice (X: Epic W F K' Ω R d k v): InkQ:= verso W K X.mesh R.draws R.paid X.c X.l X.c
abbrev advocate (X: Epic W F K' Ω R d k v):= X.paid.porter W V X.mesh X.ρ
variable {a:Finset Query}{P:ι→ magazine G d}
-- for same Pose.Fac used every evaluation.When ke.Cards open. No additional geometry of the room 
variable (Lq: Expense.Stretched L (fun i=> (q' i).mesh))
local notation "Kχ"=> (voice W K)
variable (Vt:Faculty W K (F.level d) (fun i=> (q' i).tenor W P') (fun i=> (q' i).voice W K) P L q a e )
lemma tenorEq (x: Epic W F K' Ω R d k v)(w:P'.Meets W x.mesh d): x.paid.originalT W x.mesh x.ρ 0= ( coeff 0 (deck (P'.layout W x.mesh d))) ∘ₗ (x.tenor W P' 0):=by
    rw [tenor, first_pass]; symm; ext1 i; let U:=deck (P'.layout W x.mesh d); let V:= inverseH W P' x.mesh d; exact DFunLike.congr_fun (guardsMul U V (ladderH W x.mesh d w.1).2) _ -- issue format
include Vt h M Lq
lemma pad (s:Axis)(v:Query.anchor s∈a): Faculty.NoteS Vt (fun i=> (q' i).advocate W P'):=by
    have ht:= ((P'.nested_solution W d Lq).2).mono fun i (t:_ ∧ _)=> t.1; have V':= changeFee W P' _ Vt.allowed Lq (d:=d)
    have hu:Across L q ℂ (fun i=> (q' i).paid.originalT W (q' i).mesh (q' i).ρ 0):= (rotate_b Vt.allowed (Vt.firstQ M s v (h:=h)) V').via (ht.mono (fun i p=> (tenorEq W _ p).symm))
    refine ⟨ht.mono (fun i p f=>(q' i).paid.serveT W _ _ _ (q' i).align p _ f), ht.mono (fun i p=>(q' i).paid.porter_gift W _ _ _ (q' i).align p), ?_ ⟩
    apply rotate_b Vt.allowed (rotate_b Vt.allowed V' (booth_b Vt.allowed _ hu)) (Across.solid _)
lemma pacing (w:6≤d)(s:Axis)(p: Query.crew h T S W K M s d w ⊆ a): Faculty.Before L (e+1) Vt:= Vt.seasonal h T S M w s p (Epic.pad h T S W K M q' Lq Vt s (p (Finset.mem_insert_self _ _))) -- syntax test
end Epic
end YM.SignedWilsonExpansion.Commission.Method

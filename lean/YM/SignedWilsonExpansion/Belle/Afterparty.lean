import YM.SignedWilsonExpansion.Belle.Entree
import YM.SignedWilsonExpansion.Contrast.Emerald -- Reg.Choice.Tally
/-! # Any face-polynomial BILL: physical+independent settling. includes
    customary alternating-log.Partition sum by `cumulOrder`, True word or composite. 
    Real.Pins carry cap-unit edges intact. Later post.Photos. Need phase economy. -/
set_option autoImplicit false
set_option maxHeartbeats 450000
noncomputable section
namespace YM.SignedWilsonExpansion.Belle.Entree
open FVA2 Register FVA2.Arrival Scale Scale.Jury MS MS.Menus MS.High MS.Local.Physical MS.Native MS.Land MS.Fleet
open MeasureTheory Function Filter Set XSpace XSpace.Cirrus XSpace.Normalize XSpace.Structure1 Asymptotics PowerSeries Maxwell Maxwell.Free Dframe Reg.Choice
open WickFace ProbeB Contrast
open Belle.Buffet Belle.Path WilsonCoeffUV.Mer.Xa MarqueQ Crops Belfry Belfry.ScaleFits Dancer
open scoped BigOperators Topology Classical ContDiff
variable {G:Gauge}(N:WilsonPrescription G){q: Bool}{Y:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}{S:Prescription (Press.portDeck G)}{h:G.Simple}(H: Main.Match N h Y S q) {α ι:Type}{L:Filter ι} {d n:ℕ}{p:Way G d}
variable (φ:Test n)(a:α→Tags G d n)(k: Cup α)(θ:ι→ℝ)
-- literal formula including empty convention. This specific Cup not needed for theorem. list ordering arbitrary.
abbrev slist {α:Type}[Fintype α] (p:α→Cup ι)(u:Finset α): Cup ι:= (u.toList.map p).foldr Cup.and (Cup.val 0)
abbrev tlist {α:Type}[Fintype α](p:α→Cup ι)(u:Finset α):Cup ι:= (u.toList.map p).foldr Cup.times (Cup.val 1)
def split (g:Finset (Fin n))(u:Finset (Finset (Fin n))):Prop:= u.Nonempty∧(∀ t∈u,t.Nonempty)∧ u.biUnion (fun x=>x)=g ∧ ∀ p∈u,∀ q∈u,p≠q → Disjoint p q
/-- Literal log moment with ordered set of positions. zero on empty face. -/
def cumulOrder (g:Finset (Fin n)): Cup (Finset (Fin n)):= slist ( fun (u:Finset (Finset (Fin n)))=> Cup.times ( Cup.val ( (-1:ℂ)^(u.card+1) * ↑( Nat.factorial (u.card-1) ))) (tlist Cup.cup u) ) (Finset.univ.filter (split g))
section pricing
lemma Cup.garage {F :Type}[TopologicalSpace F]{X:F→α→ℂ}{U:Set F}(L:∀ i:α, ContinuousOn (fun x=> X x i) U)(t:Cup α) : ContinuousOn (fun i=> t.dispense (X i)) U:=by
    induction t with
    | val=> exact continuousOn_const
    | cup w=> exact L w
    | and a b p q=> exact p.add q
    | times a b p q=> exact p.mul q
lemma Cup.armed (x:ι→α→ PowerSeries ℂ)(a:α→ PowerSeries ℂ)(p:∀ i:α,Harmony L (fun j=> x j i) (a i)) (v:Cup α) : Harmony L (fun j=> v.dispense (x j)) (v.dispense a):=by
    induction v with
    | val=> exact (fun i=> tendsto_const_nhds)
    | cup w=> exact p w
    | and a b p q=> exact p.add q
    | times a b p q=> exact p.mul q
end pricing
open Reg.Choice
abbrev Brings (K:Way G d)(m:ℕ)(v: Sample m→ℕ→Point G d m): Prop:= ∀ x:Scale.Stage m,∀ d:ℕ,∀ y:Tags G _ m,Tendsto (fun i=> v i d y) ( Gate x.val ) (𝓝 ( K m x d y ))
abbrev pencil (v:Sample n→ℕ→Point G d n)(i:Sample n):PowerSeries ℂ:= k.dispense fun j=> Reg.Point.story ( v i ) ( a j )
lemma forewarn {v:Sample n→ℕ→Point G d n}(t:Brings p n v)(b:ℕ): Senses (conf n) (fun i=> coeff b (pencil a k v i)) (fun i=> coeff b (formal p a k i)):=by
    intro x hx; refine Cup.armed _ _ (fun w e=>?_ ) k b; unfold Reg.Point.story; simp only [coeff_mk,Jury.fxt,dif_pos hx]; exact t (⟨x,hx⟩:Stage n) e (a w)
lemma erases {p:Way G d}{v:Sample n→ℕ→Point G d n}(t:Brings p n v)(b:ℕ)(h:XSpace.Cirrus.Centered (fun x=> coeff b ( pencil a k v x ))): Tendsto (fun m=> Deposit m (fun x=> coeff b ( pencil a k v x )) φ) Front (𝓝 ( φ.applyTo (fun y=> coeff b ( formal p a k y )) )):= Photo.sees_test _ _ _ ( conf_open n ) ( forewarn a k t b ) h φ.tsupport_subset
lemma adheres {v:Sample n→ℕ→Point G d n}(t: Brings p n v)(b:ℕ)(u:ℝ): ContinuousOn (fun x:Points n=> calcT u b ( formal p a k x )) (conf n):=by
    simp_rw [timed]; exact continuousOn_finsetSum _ fun i _=> ((forewarn a k t i).priced).mul_const _
local notation "Z"=> N.scheme
local notation "ψ" => N.criterion
abbrev W' (N:WilsonPrescription G)(n d:ℕ)(b:Sample n):ℕ→ Point G d n:=Rose.measureₓ N.scheme N.criterion d b
include H
lemma stars (d n:ℕ): Brings ( FVA2.Scale.Measure.start Z ψ d ) n ( W' N n d ):= H.startsInX d n
abbrev H' (N:WilsonPrescription G)(n d:ℕ)(b: Sample n):ℕ→Point G d n:= Speed.forms_t N.scheme N.criterion b d -- notation N shadow! notation scoped outer? audit
lemma travels (d n:ℕ): Brings ( FVA2.Scale.Measure.outlook Z ψ d ) n ( H' N n d ):=by
    intro x k p; simp_rw [H',Speed.forms_t,FVA2.Scale.Measure.outlook,Scale.Facets.actMark,Dframe.seen]; exact tendsto_finsetSum _ fun i _=> H.startsInX d n x ( i none ) ( pulseU i ( FVA2.Scale.Measure.adjust Z ψ d ) p )
end YM.SignedWilsonExpansion.Belle.Entree

import YM.AllOrder.Rosary.Puzzle
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Carillon
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext Repeat Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f L₀ : Side} {k j m π : ℕ} {K : Teller G} {p a W U V : ℝ} {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T: Tube G S} {R : RG.Rep G f} {H : Cash W p a L₀ X o U T R}
local notation "B" => radiusB p
local notation "Θ" => (Match.staple (H:=H) (J:=H) rfl rfl rfl)
-- rebased choir by changing one scalar stamp. Preserve shape, normalized conditional denominator. Not E_family homer. actual beta on block unchanged. use Station order current. Check formula highH.
variable (χ:Chi) (β γ:ℝ) {A R':PathData G}
variable (H)
def hymn : Magazine H→ Config G c→ℝ := Sum.elim (Song.sequence H Θ χ) (sounding T.down T.low β γ)
def organ : Collection.Source G c:=⟨ choir (hymn H χ β γ) ∘ pennant H,(plusone H Θ χ γ).hardRead⟩ -- check parameters order
local notation "φ"=>hymn H χ β γ
local notation "Γ"=> organ H χ β γ
variable {H} {σ C L:ℝ}{κ:Clip} (p':BudgetPoint)

lemma chord {A:PathData G}(h:A.Bounds κ σ C L)(V:Config G c) : billOf p' A.cubic V+billOf p' A.quartic V=Rosary.Weaving.highH A p' V:= by
 let f (x:Seat c):=fun i:AnalyticBridge.VerifiedReset.High=> summit A p' i 0 (x.view V)
 let u (x:Seat c) (i:ℕ):= (A.cubic i).placed p' (x.view V) 0; let v (x:Seat c) (i:ℕ):= (A.quartic i).placed p' (x.view V) 0; let w:=u; have hQ x: Summable fun i=>f x i:= summit_sum h p' (Seat.view x V) 0; change _= VerifiedReset.factor* ∑ x:Seat c, ∑' i,f x i
 have ht {k:ℕ}(R:ℕ→Atom G k)(c':ℝ) (hf : SumBudget (fun i=>(R i).budget σ) c') : billOf p' R V= VerifiedReset.factor*∑ x:Seat c,∑' i,(R i).placed p' (x.view V) 0:= by
    have hp:∀ x:Seat c,Summable fun i=> (R i).placed p' (x.view V) 0:= fun x=>(PathData.atom_dominated R p' 0 h.width hf).summable _; have hu:= allocated p' R V 1 h.width hf; simp_rw [couponA,mul_one] at hu; have hb := hu; rw [one_mul] at hb
    refine Eq.trans (b:= ∑' i:Seat c × ℕ,VerifiedReset.factor * (R i.2).placed p' (i.1.view V) 0) hb.tsum_eq.symm ?_; exact (layer_total (fun i W=> (R i).placed p' W 0) _ (fun x=>(PathData.atom_dominated R p' 0 h.width hf).summable x)).symm
 -- k fixed bug.need ht generalized
 rw [ht _ _ h.three, ht _ _ h.four]; have hz x: (∑' i, f x i)=(∑' i,u x i)+(∑' i,v x i):= Summable.tsum_sum (f:=f x) ((hQ x).comp_injective (@Sum.inl_injective ℕ ℕ)) ((hQ x).comp_injective (@Sum.inr_injective ℕ ℕ)); simp_rw [hz,sum_add_distrib, mul_add]; rfl
section essence
variable {r s z w v x y i b a' δ ℓ:ℝ}
variable (N:Captain H j r s z w v x y i b k χ)(hR:T.down.Bounds T.low σ C L) (hv: Cash.Renewed m a' δ ℓ H) (hp:p'.threshold=Pressure.temp p) (ht:p'.order ≤ j)

local notation "Z★"=> posting p' H
local notation "U₀"=> Listing.read Z★ Γ
open Refrain
include N hR hv hp ht
lemma corpus (V:Config G c): (U₀).additive p' V=-(Real.log (H.homesteadPool χ V)) + (-(γ*Collection.receipt T.down T.low p' V+(β*Rosary.Weaving.highH T.down p' V+billOf p' T.down.loop V))):= by
 rw [← chord p' hR]; apply ((pennant H).hasSum_iff.mpr (voices _ (φ) _ V _ ?_)).tsum_eq
 intro x; let W:=x.view V; have he:= HasSum.sum (f:=fun i=> masked p'.threshold (scaleT p' H i|>.support) (φ i) W) (summon p' H Θ χ N hp ht hv W) (literalScore T.down T.low p' W β γ hR); unfold W at he; rw [harmony χ hv V x,Seat.view, Collection.receipt, layer_spread, bill_spread p' _ hR.width hR.three, bill_spread p' _ hR.width hR.four,bill_spread p' _ hR.width hR.two] at he; exact he
omit hv
include hv
-- inChannels any flags embraced. Taking path-gamma=β increment proposed, compute EXACT.
variable (K':Forest S.ratio)
abbrev hallelujah (β g:ℝ)(X:Listing G c)(v:Collection.Source G c)(R:PathData G)(F:Clip)(p:BudgetPoint)(t:ℝ)(V:Config G c):=earlyValue X R F p v β t g V* Real.exp (-g*Rosary.Weaving.highH R p V)
lemma noted (V:Config G c): S.push R.beta R.eval V= hallelujah R.beta γ Z★ (organ H χ (R.beta+γ) γ) T.down T.low p' (Song.weighty H χ K') V:= by
 let X:=(plusone H Θ χ γ); let Y:=(Z★).read (X); let Z:=organ H χ (R.beta+γ) γ; let z:= Song.weighty H χ K'; have he:= Song.forward p' H Θ χ γ N K' hp ht hR hv V -- implicit θ
 have ha: plusone H Θ χ γ= organ H χ R.beta γ:= rfl; let f(β':ℝ):= organ H χ β' γ
 rw [← he,ha]; unfold hallelujah earlyValue Rep.eval Rep.exponent; simp only [Collection.frozen]; rw [corpus χ R.beta γ p' N hR hv hp ht, corpus χ (R.beta+γ) γ p' N hR hv hp ht];
 -- straightforward `gas` same; commute before operating.Explain
 rw [← show ((Z★).read (organ H χ R.beta γ)).gas p' V=((Z★).read (organ H χ (R.beta+γ) γ)).gas p' V from rfl]; simp only [mul_right_comm (_:ℝ) (((Z★).read (organ H χ R.beta γ)).gas p' V) _, ← Real.exp_add]; congr 2; ring
end essence
end YM.AllOrder.Carillon

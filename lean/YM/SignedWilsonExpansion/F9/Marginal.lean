import YM.SignedWilsonExpansion.F9.MvBill
/-! # Live deltas from Staff quotation -/
set_option autoImplicit false
set_option maxHeartbeats 630000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Wilson Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries XSpace
open Supply Ticket Polestar Next.Foundations Patrol Shard.Plan
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{J:Type*}{e k m c v b N M i j l r d n :ℕ}
variable {B Q D Z X Y η a ρ:ℝ}{E W WRED:Credit}{P:Era G ℝ}{R:Realm G (e+1) E}
local notation "κ'"=> ((n+1)*k)
namespace MarqueQ.Crops
open SignedWilsonExpansion.Commission MarqueQ MarqueQ.PorchK Asymptotics FPS Tape
variable {V:Type}[AddCommGroup V][Module ℂ V][FiniteDimensional ℂ V]
variable {ι:Type} {L: Filter ι}{g X B I' C :ι→ℝ}{Z:ι→ InkQ} (h:Maxer L X)
variable {T S:ι→ Tape.Table V n}{A':ι→Fin n→ Tape V}
include h
lemma charge_many (S:Finset J)(v:J→ι→ InkQ)(C:J→ι→ℝ)(f:∀ i∈S,charge k L X ( C i ) (v i)) : charge k L X (∏ i∈S,C i) (fun a => ∏ i∈S,v i a):=by
    induction S using Finset.induction_on with
    | empty=> simp only [Finset.prod_empty]; exact fun i _=> Wage.unitC _
    | insert i S u ih=> simp only [Finset.prod_insert u]; exact charge.mul h (f _ (Finset.mem_insert_self ..)) (ih (fun i a=>f i (Finset.mem_insert_of_mem a)))
lemma charge_sum (W:Finset J)(v:J→ι→ InkQ)(f:∀ i∈W,charge k L X C (v i)) : charge k L X C (fun a => ∑ i∈W,v i a):=by
    intro i p; simp_rw [map_sum]; exact Wage.sum h _ _ (fun i h=> f i h _ p) -- C var
lemma coolerPay (q:ι→InkQ)(x:ι→InkQ)(s: ∀ i,constantCoeff (x i)=0)(c:charge k L X 1 x)(z:charge k L X B q): charge k L X B (fun i=>(q i).subst (x i)):=by
    intro l v; simp_rw [ FPS.coeff_substituted _ (s _) ]; apply Wage.sum h; intro i hx; have h':i ≤ l:= Nat.le_of_lt_succ ( Finset.mem_range.mp hx ); simpa only [mul_one,smul_eq_mul] using Wage.mul (z i (h'.trans v)) (charge.pow h c i l v)
include h
lemma warp_margin (C:Fin n→ι→ℝ) (s:∀ i, constantCoeff (Z i)=0) (c:charge e L X 1 Z)(pA:∀ a:Fin n→V,charge e L X B (fun i=>archive (T i) a - archive (S i) a))(a:∀ i j,j≤e → Salary L X (C i) ℂ (fun v=> A' v i j)):
    charge e L X ((∏ i,C i)*B) (fun i=> Taught.ruler (Z i) (T i) (A' i) - Taught.ruler (Z i) (S i) (A' i)):=by
    let J:= Module.finBasis ℂ V; let f:= fun p: Fin n→ Fin (Module.finrank ℂ V)=> J ∘ p
    let U(i:Fin n) (p:Fin (Module.finrank ℂ V))(x:ι):= Tape.nearC J p (A' x i); have he(p):= coolerPay h (fun i=> archive (T i) (f p)-archive (S i) (f p)) _ s c (pA (f p)) -- p shadow
    let D p i:= (archive ( T i ) (f p)-archive ( S i ) ( f p ) ).subst (Z i); have hd(p i): archive (composed (T i) (Z i)) (f p)-archive (composed (S i) (Z i)) (f p)= D p i:=by unfold D; rw [←comp_clock _ _ (s i),←comp_clock _ _ (s i),← coe_substAlgHom (HasSubst.of_constantCoeff_zero' (s i)),map_sub] -- coe_all?
    unfold Taught.ruler; simp_rw [prices_ar ( Tape.composed _ _ ) _ J, ← Finset.sum_sub_distrib, ← mul_sub]; refine charge_sum h _ _ (fun i _=> charge.mul h (charge_many h _ (fun j x=> U j (i j) x) C (?_)) (?_)); -- elabor
    · intro j _ v hv; simp_rw [U,nearC_pay]; exact a j v hv (J.coord _)
    change charge _ _ _ B (fun v=> archive (Tape.composed (T v) (Z v)) (f i)- archive (Tape.composed (S v) (Z v)) (f i)); simp_rw [hd]; exact he i
end MarqueQ.Crops
end YM.WilsonCoeffUV.Mer.Xa

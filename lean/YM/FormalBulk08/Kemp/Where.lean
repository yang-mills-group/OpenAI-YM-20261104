import YM.FormalBulk08.Kemp.Shelf

/-! One transported mark, prior to preimage average and coordinate resets. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Kemp
open Reef Lava Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 PowerSeries Bank
open Stationary Lotus Shore Mesa Gorge City Cork Rift Next.Free Flat RG Precision Tree
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge} {I J: Type*} {η θ A B : ℝ} {l i u j t r : ℕ}
variable (K : KernelChoices)(P:Flight j t)(V:Lodge P.patch)(W Z:Pot G)(ρ : ChartRatio G)
variable {K} (h:P.patch.Branches K G)
-- moving inputs already on patch shelf
lemma convict (hv:Young Z l):Young (coves K P V Z) l:= by
   intro e r he; apply hv; intro hh; unfold coves Glide.urn at he; rw [hh,jetty_zero,pearl_zero,pearl_zero,pearl_zero] at he; contradiction
lemma convict_tor (hv:Young Z l)(hZ:∀ e r,Agate (Z e r))(hf:l≤u)(n:Side)(hs:0 < η)(hp:0≤A)(hk:(Flight.duo K.penalty P).A0.strip η A): Young (rancho (sailors P V h Z u n)) l := by
   intro e r he; apply hv; intro hh; rw [fees_tor P V Z h hv hZ hf _ _ _ hs hp hk,altitude,hh,jetty_zero,sieve_zero,pearl_zero,pearl_zero,pearl_zero] at he; contradiction
lemma convict_base (hv:Young Z l)(hZ:∀ e r,Agate (Z e r))(hf:l≤u)(n:Side)(ht:4≤ t) :
   Young (rancho (lever (ferry P h V n) (Reef.seat (Reef.floor K P V n) (banner u Z _)))) l:= by
    obtain ⟨s,C,h₁,h₂,H⟩:=aone P (K:=K) G ht; intro e r he; apply convict_tor P V Z h hv hZ hf n h₁ h₂ H; intro hz; unfold sailors at hz; rw [infer_joust (saddleP G (primary P.patch K n) V) _ _ _, show rancho _ _ _=_ from hz,jetty_zero] at he;contradiction

def border := dipper (lands (rayshot P V h)) (magma P V W ρ h) (coves K P V Z)
def braise (u:ℕ):Pot G:=fun e r=> ∑ i∈ Finset.range (u+3*e+1), jetty (coastRight _ _ _) (border P V W Z ρ h i e r)
def calendarQ (k:ℕ) (n:Side)(a:(primary P.patch K n).Choices):=dipper ((rayshot P V h).acts n) (whirl P V W ρ h n a) (rancho (sailors P V h Z k n))

lemma truss (vivid: Vivid W)(hr:LocalRatio ρ)(hz:Young Z l)(u:ℕ):Young (braise P V W Z ρ h u) l:= by
    intro e r he; by_contra hv; apply he; unfold braise; refine Finset.sum_eq_zero fun i _=> ?_; have hh:border P V W Z ρ h i e r=0:=by by_contra hP; exact hv ((youth_egg _ (convict (K:=K) P V Z hz) (fairy W ρ P V K vivid hr) _ _ _ hP).1)
    rw [hh,jetty_zero]
lemma truss_rite (hp:Story W (pink K.penalty P.wing))(hr: LocalRatio ρ)(ht:4≤t)(hz:Young Z l)(u)(hZ:∀ e r,Agate (Z e r))(he:l≤u)(e r)(n:Side)(k:(primary P.patch K n).Choices) :
    rancho (tossed P ρ h V n k (stone W _) (banner u Z _)) e r=∑ i∈Finset.range (u+3*e+1), jetty (coastRight _ _ _) (calendarQ P V W Z ρ h u n k i e r) := by
   let F:= ferry P h V n;let S:= primary P.patch K n;let E:= saddleP G S V; let p:= flush (Reef.floor K P V n) k ρ (Mesa.stone W _);let J:= Reef.seat (Reef.floor K P V n) (banner u Z _)
   let A:=rancho (cobalt F p);let B:=rancho (coffer W ρ P V h n k)
   obtain ⟨s,C,hσ,hC,hf⟩:=aone P (K:=K) G ht; obtain ⟨v,B',hv,hB,H₀,-⟩:= colors G K.penalty K.penalty_pos P.legal
   have hχ:=bath_vac P V W ρ h n k hp.toVivid hr hσ hC hf
   have hx : Solved F p:= consolidate P ρ h V n hr k (Mesa.stone W _) (stoned_main hv.le hB.le (H₀ P.wing).1 hp.toVivid hp.ink _) ht
   have hA : ∀ e r,A e r=jetty E (B e r):= fun a b=> infer_joust E _ _ _
   let q:= aqua F.saddle (I:=wire G n); let Q: Matrix _ _ ℝ:= (rayshot P V h).acts n
   have hq(k u): Q (E k) (E u)= q k u:= ray_forms ..
   let Z':= rancho (lever F J)
   have HE a b:= infer_joust E (lever F J) a b; have hL : ∀ i j k, swim q A i j k=jetty E (swim Q B i j k):= fun i j k=> (dye_swim E q Q hq B A hA i j k).symm
   unfold tossed; rw [extraction_mark F p J hx hχ (convict_base P V Z h hz hZ he n ht) _ _ (u+3*e) (by omega)]; refine Finset.sum_congr rfl fun i hi=>?_ ;rw [← show jetty E (calendarQ P V W Z ρ h u n k i e r)= _ from dye_dip E q Q hq (swim Q B) (rancho (sailors P V h Z u n)) (swim q A) Z' hL HE _ _ _];rfl
lemma tossed_gen (hp:Story W (pink K.penalty P.wing))(hr:LocalRatio ρ)(ht:4≤t)(hz:Young Z l)(u)(hZ:∀ e r,Agate (Z e r))(he:l≤u)(n:Side)(k:(primary P.patch K n).Choices): Young (rancho (tossed P ρ h V n k (stone W _) (banner u Z _))) l:= by
    intro e r hv; by_contra hh;rw [truss_rite P V W Z ρ h hp hr ht hz _ hZ he] at hv; apply hv; apply Finset.sum_eq_zero; intro i _; obtain ⟨s,C,h₁,h₂,H⟩:=aone P (K:=K) G ht
    have ht':calendarQ P V W Z ρ h u n k i e r=0:= by by_contra hv;exact hh ((youth_egg _ (convict_tor P V Z h hz hZ he n h₁ h₂ H) (fiat P V W ρ h n k hp.toVivid hr h₁ h₂ H) _ _ _ hv).1)
    rw [ht',jetty_zero]
end YM.FormalBulk08.Kemp

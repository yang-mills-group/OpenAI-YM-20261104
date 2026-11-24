import YM.Integration.WilsonThermometerInversionStation
import YM.PertExtension.SlotSlope

/-! Angular pole extraction on the deployed sources. At the minimal
radial grade each live plaquette contributes its genuine linear curl in
the original translated location. A higher-rank word has zero head. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerInversionHead
open Function Filter Finset Set Lattice Wilson RG Source Labels
open PhysicalNext.Repeat.Legato PertExtension PertExtension.Orb PertExtension.Orb.SlotEvaluation
open PertExtension.Chart PertExtension.Series PertExtension.Series.Tested PertExtension.Series.Radial PertExtension.LatticePT
open WilsonOriginalStarSceneWords WilsonThermometerDeclaredSeeds WilsonThermometerInversionSockets
open scoped ContDiff Topology Classical BigOperators

variable {G:Gauge} (R:Run G) {V T:Type} (d:V→ℕ) {n:Side}

def polar (i:Entry R d) (z:Site n) (u:Dir G n) :=
  ∑ b:Fin (rank R d i)→G.ColorIndex, (raw R d i).coeff b *
    ∏j:Fin (rank R d i),Slope.leg z ((raw R d i).leg j,b j) u

private theorem curl (i:Entry R d) (z:Site n) (u:Dir G n) :
    Tendsto (fun t:ℝ=>t⁻¹^(rank R d i)*(raw R d i).unmasked (representative (t • u)) z)
      Tested.germ (𝓝 (polar R d i z u)) := by
  let a:=raw R d i
  let k:=rank R d i
  have term (b:Fin k→G.ColorIndex) := tendsto_finsetProd univ (fun j _=>Slope.legible z u (a.leg j,b j))
  have he:=tendsto_finsetSum univ (fun b _=>(tendsto_const_nhds (x:=a.coeff b)).mul (term b))
  apply he.congr'
  filter_upwards with t
  change (∑ b:Fin k→G.ColorIndex,a.coeff b*∏j:Fin k,t⁻¹*field (a.leg j) z (b j) (t • u))=_
  change _=t⁻¹^k*∑ b:Fin k→G.ColorIndex,a.coeff b*∏j:Fin k,field (a.leg j) z (b j) (t • u)
  rw [mul_sum]
  exact sum_congr rfl fun b _=>by rw [prod_mul_distrib];simp only [prod_const,card_univ,Fintype.card_fin];ring

def selected (i:Entry R d) (z:Site n) (u:Dir G n) :=
  if pole R d i = rank R d i then polar R d i z u else 0

theorem read (i:Entry R d) (z:Site n) (u:Dir G n) :
    Tendsto (fun t:ℝ=>t⁻¹^(pole R d i)*(raw R d i).unmasked (representative (t • u)) z)
      Tested.germ (𝓝 (selected R d i z u)) := by
  have credit:=low R d i
  by_cases eq:pole R d i=rank R d i
  · simpa [selected,eq] using curl R d i z u
  let q := rank R d i-pole R d i
  have qp:q≠0 := Nat.ne_of_gt (Nat.sub_pos_of_lt (lt_of_le_of_ne credit eq))
  have add : pole R d i+q =rank R d i := Nat.add_sub_of_le credit
  have h0 : Tendsto (fun t:ℝ=>t^q) Tested.germ (𝓝 (0:ℝ)) := by
    simpa only [zero_pow qp] using ((continuous_pow q).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : nhdsWithin (0:ℝ) (Ioi 0) ≤ 𝓝 0))
  have hm:=h0.mul (curl R d i z u)
  rw [selected,if_neg eq,←zero_mul (polar R d i z u)]
  apply hm.congr'
  filter_upwards [Tested.eventually_pos] with t ht
  have scale : t^q*t⁻¹^(rank R d i)=t⁻¹^(pole R d i) := by
    rw [←add,pow_add,inv_pow,inv_pow]
    field_simp
  change t^q*(t⁻¹^(rank R d i)*_)=t⁻¹^(pole R d i)*_
  rw [←mul_assoc,scale]

variable (s:Finset V) (b:(j:V)→Choice R d j) (o:V→Site n) (g τ:ℝ)
  (v:(j:V)→R.family.label (d j)) (t:V→T→ℂ) (x:T) (L:ℂ→L[ℝ]ℝ)
local notation "O" => WilsonThermometerInversionSockets.word R d s b o g τ v t x L
local notation "w" => WilsonThermometerInversionSockets.charge R d s b
local notation "e" j:max => entry R d j (b j)

theorem radial (u:Dir G n) :
    jet ((restrictedO (O)) ∘ expLinks G (Cotree n)) (w) u =
      L (∏j∈s,t j x*scalar R d g τ v (e j)) * ∏j∈s,selected R d (e j) (o j) u := by
  obtain ⟨hp,hv⟩:=incoming R d s b o g τ v t x L
  have hl:= (directions hp.curved.germ u).shift («w»:=(w)) (fun i hi=>by
    rw [jets_vanish hp.curved.germ hv hi];rfl)
  have hx:=hl.tendsto_first
  simp only [Nat.add_zero] at hx
  have hd:=tendsto_finsetProd s (fun j _=>read R d (e j) (o j) u)
  have hr: Tendsto (fun r:ℝ=>r⁻¹^(w)*(O) (representative (r • u))) Tested.germ
      (𝓝 (L (∏j∈s,t j x*scalar R d g τ v (e j))*∏j∈s,selected R d (e j) (o j) u)) := by
    apply (hd.const_mul _).congr'
    filter_upwards with h
    unfold WilsonThermometerInversionSockets.word charge
    simp only [prod_mul_distrib,prod_pow_eq_pow_sum]
    ring
  exact tendsto_nhds_unique hx hr

end YM.Integration.WilsonThermometerInversionHead

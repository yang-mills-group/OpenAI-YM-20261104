import YM.Integration.WilsonConditionalTaylorBulkInlet

/-! The real Wilson noise and Haar Jacobian preserve the coupling rank and
field parity of a changed preceding action. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorBulkShape
open FormalBulk08
open Lava Gorge Shore Lattice Laurent Filter Function Lotus Orb Wick Reef Jets Series PowerSeries Stationary Wilson Next.Free
open Exterior Bloch RG Precision UVExtension.Free Work.F08 Flat Mesa Tree Work.F05 Bank
open WilsonConditionalTaylorBulkRows WilsonConditionalTaylorBulkInlet
open scoped Topology BigOperators Classical

def Ranks {I : Type} [Fintype I] (U : Pap I) : Prop := ∀ e r, 0 < e → rancho U e r≠0 → r ≤ e+2 ∧ r%2=e%2

variable {G : Gauge} {K : KernelChoices} {j t : ℕ} (P : Flight j t) (L : Lodge P.patch) (ρ : ChartRatio G)
    (h : P.patch.Branches K G) (n : Side) (k : (primary P.patch K n).Choices) (U : Pap (wire G (n*P.L)))

theorem paid (ht : LocalRatio ρ) (room : 4 ≤ t) (prior : Ranks U) : Fiery (rancho (inlet P L ρ h n k U)):=by
  obtain ⟨s,b,hs,hb,hu⟩:=aone P (K:=K) G room
  intro e r he
  rw [moved P L ρ h n k U e r hs hb hu] at he
  split at he
  · contradiction
  rename_i hE
  by_contra! hx
  let S:=primary P.patch K n
  let F:=Reef.floor K P L n
  let H:=joust (saddleP G S L)
  have hg:0 < e:=Nat.pos_of_ne_zero hE
  have hw:rancho U e r=0:=by by_contra hh;have grant:=prior e r hg hh;omega
  let Z:=noisePin S k (G:=G)
  have hz:rancho Z e r=0:=by
    unfold Z noisePin rancho
    rw [after_one,marble_eq_zero_iff,MvPolynomial.homogeneousComponent_of_mem (paste_grade _ _),if_neg (by omega)]
  have haar : rancho (H (halo (sap F ρ) (wire G n))) e r=0:=by
    apply (Bank.quake _ _ _ r).mp;apply vacant
    have hv:=sap_root F ρ ht
    unfold rancho
    rw [marble_eq_zero_iff,MvPolynomial.homogeneousComponent_of_mem
      (log_grade (p:=paste (sap F ρ)) (by rw [paste_first,hv,map_one]) (paste_grade (sap F ρ)) e),if_neg (by omega)]
  have real : rancho (H (flush F k ρ U)) e r=0:=by
    unfold H;rw [mirror_in ρ S L k U];unfold rancho
    rw [map_add,marble_add,show marble _ _=0 from haar,add_zero];apply match_cap
    unfold rancho;rw [map_sub,←canyon_eq,map_sub];simp_rw [canyon_eq]
    rw [show marble r (coeff e (joust (staging G S) (PowerSeries.map (MvPolynomial.rename Sum.inl).toRingHom U)))=0 from
      (Bank.quake _ (staging G S) e r).mp (vacant Sum.inl U e r hw),
      show marble _ _=0 from (Bank.quake _ (staging G S) _ _).mp hz,sub_zero]
  exact he (by rw [show rancho _ _ _= _ from real,pearl_zero])

theorem output (ht : LocalRatio ρ) (room : 4 ≤ t) (prior : Ranks U)
    (head : coeff 0 U=crunch (kernelP G K.penalty P.wing _)) : Ranks (Reef.landed P ρ h L n k U):=by
  have fuel := paid P L ρ h n k U ht room prior
  intro e r positive nonzero
  obtain ⟨e,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  rw [WilsonConditionalTaylorBulkRows.read P L ρ h n k U ht room head fuel e r] at nonzero
  by_contra! cold
  apply nonzero
  unfold connected
  apply Finset.sum_eq_zero
  intro i _
  have vanished : swim ((rayshot P L h).acts n) (rancho (inlet P L ρ h n k U)) i (e+1) r=0:=by
    by_contra spanned
    obtain ⟨_,field,parity,_⟩:=thermal _ fuel i (e+1) r spanned
    omega
  rw [vanished,jetty_zero]

end YM.Integration.WilsonConditionalTaylorBulkShape
end


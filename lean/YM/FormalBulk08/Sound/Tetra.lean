import YM.FormalBulk08.Sound.Kernel
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Sound
open Lattice Laurent Bloch RG Precision Wilson Orb Reef City Filter Function Series Wick Jets Stationary Lotus Shore Lava Gorge Mesa Cork Wine Flat Glide Bank Work.F08 Next.Free Chapel Rift Aster Dove Dove.Lab PowerSeries UVExtension UVExtension.Free Matrix Exterior Tree North
open scoped Topology ENNReal BigOperators Classical Matrix
variable {G:Gauge}{I J:Type}{A:Levels G}{K:KernelChoices}{d j t:ℕ}{W:Lab G K I}{ρ:ChartRatio G}
variable (x:Leaf W.scrolls)(n:Side)
abbrev zeta :=saddleP G (boxS x n) (W.wood x.a x.b)
def covant := Matrix.fromBlocks (1:Matrix (PinL x n) (PinL x n) ℝ) (show Matrix (PinL x n) (wire G n) ℝ from conditionalV x n) 0 (1:Matrix (wire G n) (wire G n) ℝ)
lemma covanted (i j) :(limY x).acts n (zeta x n i) (zeta x n j)= covant x n i j := by
    unfold zeta limY saddleP; rw [Equiv.trans_apply,Equiv.trans_apply, dye_spot,acts_unit,acts_unit,deadActs]; cases i <;> cases j <;> first|rfl|simp [Matrix.one_apply,covant]
variable (hp:Use W ρ d)
lemma turned (p : Pap (PinL x n ⊕ wire G n)) : joust (zeta x n) (lever (hospital x n hp) p)=PowerSeries.map (mixRows ((limY x).acts n)).toRingHom (joust (zeta x n) p) := by
   rw [sash_lever (hospital x n hp) p (conditionalV x n) rfl]; apply mix_pane; exact covanted x n
lemma swarm (i j): (limG x).acts n (zeta x n i) (zeta x n j)= aqua (hospital x n hp).saddle i j:= by unfold zeta saddleP limG; rw [Equiv.trans_apply,Equiv.trans_apply,dye_spot, deadActs,deadActs,deadActs]; cases i <;> cases j <;> rfl
include hp in
lemma pastured (i j):(limG x).acts n i j=(limG x).acts n j i:=by
    obtain ⟨i,rfl⟩:= (zeta x n).surjective i; obtain ⟨j,rfl⟩:= (zeta x n).surjective j; rw [swarm x n hp,swarm x n hp]; exact aqua_symm ..
lemma spire_materials (p : Pap (PinL x n⊕wire G n)) (e r):
      rancho (joust (zeta x n) (cobalt (hospital x n hp) p)) e r= if e=0 then 0 else pearl ((limY x).acts n) (rancho (joust (zeta x n) p) e r) := by
    by_cases hx:e=0
    · subst e; unfold rancho joust; rw [coeff_map,cobalt_base,map_zero,marble_zero,if_pos rfl]
    unfold rancho;rw [if_neg hx,cobalt,show joust _ (_-_) = joust _ _- joust _ _ from map_sub (PowerSeries.map _) _ _, map_sub,show joust (zeta x n) (.C _) = _ from PowerSeries.map_C _ _,PowerSeries.coeff_C,if_neg hx,sub_zero, turned x n hp,coeff_map]; exact Lava.target ..
def restoration (T:Pot G):=stone T (n*(W.pat x).L) -- opaque
abbrev joy (T:Pot G)(k:(boxS x n).Choices): Pap (PinL x n⊕wire G n):= flush (rug x n) k ρ (stone T (n*(W.pat x).L))
def harvestF (T:Pot G)(k:(boxS x n).Choices):= joust (zeta x n) (cobalt (hospital x n hp) (joy (ρ:=ρ) x n T k))
lemma wealth (T:Pot G)(p:Vivid T)(k:(boxS x n).Choices)(ht: LocalRatio ρ): Fiery (rancho (harvestF x n hp T k)) := by
   intro e r he; unfold harvestF at he; rw [spire_materials x n hp] at he; split at he
   · contradiction
   rename_i hE;by_contra! hx;let S:= boxS x n; let U:= Mesa.stone T (n*(W.pat x).L); let F:=rug x n; let H:=joust (zeta x n); have hg:0<e:=Nat.pos_of_ne_zero hE
   have hw : rancho U e r=0:= by
      rcases r with (_|r)
      · unfold U rancho; rw [marble_eq_zero_iff,sow_coeff,sow,map_sum]; apply Finset.sum_eq_zero; intro i _; rw [MvPolynomial.homogeneousComponent_of_mem (facade_grade _ _),if_neg (by omega)]
      unfold U;rw [p.flower _ (r+1) 0]; have hL : T e (r+1)=0:= by by_contra H; have ha:=p.valence _ _ H;omega
      rw [hL,cum_zero]
   let Z:= (noisePin S k (G:=G)); have hz : rancho Z e r=0 := by
       unfold Z noisePin rancho;rw [after_one,marble_eq_zero_iff,MvPolynomial.homogeneousComponent_of_mem (paste_grade _ _),if_neg (by omega)]
   have h₁ : rancho (H (Jets.halo (sap F ρ) (wire G n))) e r=0:= by
       apply (Bank.quake _ _ _ r).mp; apply vacant
       have hv:= sap_root F ρ ht; unfold rancho; rw [marble_eq_zero_iff, MvPolynomial.homogeneousComponent_of_mem (log_grade (p:=paste (sap F ρ)) (by rw [paste_first,hv,map_one]) (paste_grade (sap F ρ)) e),if_neg (by omega)]
   have hR : rancho (H (flush F k ρ U)) e r=0 := by
       change rancho (joust _ _) _ _=0;rw [show joust (zeta x n) (flush F k ρ U)=_ from Bank.mirror_in ρ S (W.wood x.a x.b) k U]; unfold rancho;rw [map_add,marble_add,show marble _ _=0 from h₁,add_zero];apply match_cap
       unfold rancho; rw [map_sub,←canyon_eq,map_sub];simp_rw [canyon_eq]; rw [show marble _ _=0 from (Bank.quake _ _ _ _).mp (vacant _ U _ _ hw), show marble _ _=0 from (Bank.quake _ (staging G S) _ _).mp hz,sub_zero]
   exact he (by rw [show rancho _ _ _= _ from (show rancho (joust (zeta x n) (joy (ρ:=ρ) x n T k)) e r=0 from hR),pearl_zero])
end YM.FormalBulk08.Sound

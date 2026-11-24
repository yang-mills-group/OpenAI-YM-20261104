import YM.FormalBulk08.Bank.River

/-! Coeff arrays stage in cover positions. Assembly BEFORE canonical projection;
no rank-zero storage. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Bank
open Lava Gorge Shore Lattice Laurent Filter Function Lotus Orb Wick Reef Jets Series PowerSeries Stationary Wilson Next.Free
open Exterior Bloch RG Precision UVExtension.Free Work.F08 Flat Mesa Tree Work.F05
open scoped Topology ENNReal BigOperators Classical ContDiff
variable {G : Gauge} {n f : Side} (S : StepData n f) {P : Patch} {L : Lodge P}
   (T : Pot G) (ρ: ChartRatio G)

def ouzo (P : Patch) (L : Lodge P) (K : KernelChoices) (e r : ℕ) : Tile (Biglot (BoardL G P L)) r:=
    pearl (lands (pane G P L)) (atlas P T e r- TO G P K e r) + WO P L ρ e r -- fill
lemma mirror_in (S : StepData n f) (F : Lodge S.patch) (k : S.Choices) (p : Pap (wire G f)) : joust (saddleP G S F) (flush F.forest k ρ p)=
   PowerSeries.map (mixRows ((pane G S.patch F).acts n)).toRingHom (joust (staging G S) (PowerSeries.map (MvPolynomial.rename Sum.inl).toRingHom p)-joust (staging G S) (noisePin S k)) + joust (saddleP G S F) (halo (sap F.forest ρ) (wire G n)) := by
    unfold flush; rw [show joust _ (_+_)= joust _ _+ joust _ _ from map_add (PowerSeries.map _) _ _,becoming S F];unfold vacuumU joust;rw [map_sub]
lemma filtered (hK : S.patch.Branches S.kernel G) (hT : Vivid T) (hr : LocalRatio ρ) (F : Lodge S.patch) (k : S.Choices) (e r : ℕ) (i : Fin r) :
   rancho (joust (saddleP G S F) (flush F.forest k ρ (stone T f))) e r=
     pearl ((pane G S.patch F).acts n) (pearl ((winging (Rim G S.patch) (Loc G 1)).acts n) (cum i n (altitude S.patch T e r)) -cum i n (TO G S.patch S.kernel e r))+cum i n (WO S.patch F ρ e r) := by
   rw [mirror_in, WO_tor G S ρ F hr, TO_tor G S k hK,← tor_yarns S T hT]
   unfold rancho; rw [map_add,marble_add,coeff_map]; congr 1; change marble r (mixRows _ _)=_; rw [Lava.target,map_sub];simp_rw [←canyon_eq,map_sub]
variable {S} {K : KernelChoices} {j t : ℕ} (F : Flight j t) (R : Lodge F.patch)
def cola (K : KernelChoices) : OrbitV (Biglot (BoardL G F.patch R)) := fun e r=> if e=0 then 0 else pearl (lands (zealand K F R G)) (ouzo T ρ F.patch R K e r)

def coffer (h : F.patch.Branches K G) (n : Side) (k : (primary F.patch K n).Choices) :=
   joust (saddleP G (primary F.patch K n) R) (cobalt (ferry F h R n) (flush (Reef.floor K F R n) k ρ (stone T _)))
lemma posted (h : F.patch.Branches K G) (n : Side) (k : (primary F.patch K n).Choices) (e r : ℕ) {σ C : ℝ} (hs : 0<σ) (hc:0≤C) (H : (Flight.duo K.penalty F).A0.strip σ C) :
    rancho (coffer T ρ F R h n k) e r= if e=0 then 0 else pearl ((zealand K F R G).acts n) (rancho (joust (saddleP G (primary F.patch K n) R) (flush (Reef.floor K F R n) k ρ (stone T _))) e r) := by
   by_cases hx:e=0
   · subst e; unfold rancho coffer joust;rw [coeff_map,cobalt_base,map_zero,marble_zero,if_pos rfl]
   unfold rancho coffer; rw [if_neg hx,cobalt,show joust _ (_-_) = joust _ _- joust _ _ from map_sub (PowerSeries.map _) _ _, map_sub,show joust (saddleP _ _ _) (.C _) = _ from PowerSeries.map_C _ _,PowerSeries.coeff_C,if_neg hx,sub_zero]
   rw [shifted F R h n _ σ C hs hc H,coeff_map]; exact Lava.target ..
lemma fairy (K : KernelChoices) (hT : Vivid T) (hr : LocalRatio ρ): Fiery (cola T ρ F R K) := by
   intro e r h; unfold cola at h;split at h
   · contradiction
   rename_i he;by_contra! hh
   have hx : T e r=0:= by by_contra hV;have hp:=hT.valence _ _ hV;omega
   have hv := WO_vanish G ρ hr R e r (Or.inl (show e≠r by omega))
   unfold ouzo atlas altitude at h; rw [hv,TO_vanish _ _ _ _ _ (by omega),hx,jetty_zero,pearl_zero,sub_zero,pearl_zero,zero_add,pearl_zero] at h;contradiction
end YM.FormalBulk08.Bank

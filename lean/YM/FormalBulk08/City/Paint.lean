import YM.FormalBulk08.City.Noble

/-! Color equations for ALL e/r potential kernels. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.City
open Reef Lava Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 PowerSeries
open Lotus Shore Mesa Gorge
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} (g : G.El) {m r : ℕ} {n : Side}

def suit : Matrix (hue G) (hue G) ℝ:= LinearMap.toMatrix' (((moon G).symm.toLinearEquiv.toLinearMap.comp (G.adjoint g)).comp (moon G).toLinearEquiv.toLinearMap)
lemma shy (b : G.Color) : suit g *ᵥ ((moon G).symm b)= (moon G).symm (G.adjoint g b) := by
   rw [suit,LinearMap.toMatrix'_mulVec]; simp
def pointL (n:Side):Matrix (wire G n) (wire G n) ℝ:= fun i j=> if i.1=j.1 ∧ i.2.1=j.2.1 then suit g i.2.2 j.2.2 else 0
def armature (n:Side): Rays (wire G n)→L[ℝ]Rays (wire G n):= LinearMap.toContinuousLinearMap (pointL g n).mulVecLin
lemma seated (j:Edge (Site n))(Z): Stationary.arm G n 1 (armature g n Z) (j.1,coord j.2) = G.adjoint g (Stationary.arm G n 1 Z (j.1,coord j.2)):= by
   ext b; let U:=Stationary.arm G n 1 Z (j.1,coord j.2)
   change (∑ v:wire G n,pointL g n (j.1,coord j.2,b) v * Z v)=(moon G).symm (G.adjoint g U) b
   rw [←shy,Fintype.sum_prod_type,Finset.sum_eq_single j.1,Fintype.sum_prod_type, Finset.sum_eq_single (coord j.2)]
   · apply Finset.sum_congr rfl; intro i _; rw [pointL,if_pos (And.intro rfl rfl)];rfl
   · intro k _ H;simp [pointL,Ne.symm H]
   · simp
   · intro k _ H;simp [pointL,Ne.symm H]
   simp
lemma court (p:Pap (wire G n))(h:Rite p p 1 0)(e r): rancho p e r=pearl (pointL g n) (rancho p e r):= by
   let R:=armature g n
   have hp (x) : Stationary.input G n (R x) = Lattice.gauge (fun _=>g) (pull 1 0 (Stationary.input G n x)) := by
      funext b; rw [pull_id,Lattice.gauge,Stationary.input,represent_link,Stationary.input,represent_link]; unfold R; rw [seated];apply G.mat_injective; simp [Gauge.conjugate]; exact G.exp_conjugate g _
   have he := h (wire G n) (fun z:Rays (wire G n)=>z ∘ id) R (fun _ _=>g) rfl (map_zero R) contDiffAt_id R.contDiff.contDiffAt (fun _=>contDiffAt_const) ⟨g,rfl⟩ (.of_forall hp)
   rw [Bank.pane_letter (pointL g n) R R.contDiff.contDiffAt rfl] at he
   have hx:=congr_arg (coeff e) he;rw [fit_translate] at hx;simp only [coeff_map] at hx;change MvPolynomial.rename id _=mixRows _ _ at hx;rw [MvPolynomial.rename_id_apply] at hx; unfold rancho;rw [←target]; exact congr_arg (marble r) hx
lemma unshot (T : Tile (wire G n) r) (u): pearl (pointL g n) T u = ∑ v:chain (hue G) r,T (fun i=>rowD (u i) (v i)) *∏ i,suit g (v i) (u i).2.2 := by
   let S (v:chain (hue G) r) : chain (wire G n) r:=fun i=>rowD (u i) (v i); have hs : Injective S:=fun x y he=>funext fun i=>congr_arg (fun a:wire G n => a.2.2) (congr_fun he i); let M: chain (hue G) r ↪ chain (wire G n) r:=⟨S,hs⟩
   rw [pearl,tsum_fintype,← Finset.sum_subset (Finset.subset_univ ((Finset.univ : Finset (chain (hue G) r)).map M)) ?h, Finset.sum_map]; apply Finset.sum_congr rfl; intro i _;congr 1; exact Finset.prod_congr rfl fun j _=> if_pos ⟨rfl,rfl⟩
   case h =>
     intro x _ hx; have hh : ∃ i, ¬ ((x i).1 = (u i).1 ∧ (x i).2.1=(u i).2.1):=by
       by_contra! he; exact hx (Finset.mem_map.mpr ⟨(fun i=>(x i).2.2),Finset.mem_univ _,funext fun i=>Prod.ext (he i).1.symm (Prod.ext (he i).2.symm rfl)⟩)
     obtain ⟨i,hi⟩:= hh; rw [Finset.prod_eq_zero (Finset.mem_univ i) (show pointL g n _ _=0 from if_neg hi),mul_zero]

def Lust (V : Tile (edgeL G) r) : Prop:= ∀ (g : G.El) (u : chain (edgeL G) r), V u= ∑ v:chain (hue G) r,V (fun i=>rowD (u i) (v i)) *∏ i,suit g (v i) (u i).2.2
lemma stainedL (V : Tile (edgeL G) r)(S:(n:Side)→Pap (wire G n))(j) (h:Light V (fun n=>rancho (S n) j r)) (hp : ∀ᶠ n in atTop,Rite (S n) (S n) 1 0) : Lust V:= by
   intro g u; have ht := tendsto_finsetSum (Finset.univ : Finset (chain (hue G) r)) (fun v _=> (h (fun i=>rowD (u i) (v i))).mul_const (∏ i,suit g (v i) (u i).2.2))
   refine tendsto_nhds_unique (h u) (ht.congr' ?_); filter_upwards [hp] with n hn;exact ((congr_fun (court g (S n) hn j r) (Lotus.drip n ∘ u)).trans (unshot g _ _)).symm
lemma colorful {T : Pot G} {M : Row (TypeFace 2) (TypeFace 2)} (h:Story T M) (e r)(he:0<r) : Lust (T e r) := by
   obtain ⟨u,C,hp,hC⟩:=h.fare e r; refine stainedL _ (stone T) e ?_ (.of_forall fun n=> h.civic n 1 0); simp_rw [h.flower e r (⟨0,he⟩ : Fin r)];exact (Bank.stable hp.le (h.civil e r) hC _).1
end YM.FormalBulk08.City

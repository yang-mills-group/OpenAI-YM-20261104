import YM.FormalBulk08.Chapel.Lights

/-! Multi projector price. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Chapel
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 PowerSeries Next.Free RG Precision
open Lotus Shore Mesa Gorge City Cork Rift Lava
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge}{σ η C : ℝ}{m r:ℕ}{L : Side}{I J : Type}

def snake (t: Cover)(a:chain I m)(w : cloud m):chain (Biglot I) m:= fun i=>(t+rack w i,a i)
def crown (S:Fin m→Cross L I J) (x:Cover)(t:chain I m)(w:cloud m):Tile (Biglot J) m:= fun v=> ∏ i,merit (S i) ((snake x t w) i) (v i)
lemma crown_foot (S: Fin m→ Cross L I J)(x:Cover)(t:chain I m) (i: Fin m)(u:Axis)(hp:Odd L.val):
   booth (crown S x t) (i,u)= crown (update S i (forwardC L (S i) u)) x t := by
    ext w y; unfold booth; rw [Pi.sub_apply]; unfold crown; rw [← Finset.mul_prod_erase (Finset.univ: Finset (Fin m)) _ (Finset.mem_univ i), ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), update_self]
    have he : snake x t (w+buzz (i,u)) i = ((snake x t w i).1+step u,(snake x t w i).2) := by simp [snake,rack_plus,add_assoc]
    rw [he, ← cloak (S i) hp]; let B:= (Finset.univ: Finset (Fin m)).erase i; let P:= snake x t w
    have hu : ∏ j∈B, merit (S j) (snake x t (w+buzz (i,u)) j) (y j)=∏ j∈B,merit (S j) (snake x t w j) (y j):= Finset.prod_congr rfl fun j hj=> by rw [show snake _ _ _ j=snake x t w j from (by simp [snake,rack_plus,Ne.symm (Finset.ne_of_mem_erase hj)])]
    have hz : ∏ j∈B,merit (update S i (forwardC L (S i) u) j) (snake x t w j) (y j)=∏ j∈B,merit (S j) (snake x t w j) (y j) := Finset.prod_congr rfl fun j hj=>by rw [update_of_ne (Finset.ne_of_mem_erase hj)]
    unfold B at hu hz; rw [hu,hz,Pi.sub_apply,sub_mul]

def soak (a:Fin m)(l:List (Fin m × Axis)) : List Axis:= l.filterMap fun p=> if p.1=a then some p.2 else none
lemma soak_pile (l:List (Fin m× Axis)): ∑ x:Fin m,(soak x l).length=l.length:= by
   induction l with
   | nil=> simp [soak]
   | cons a l ih=>
      have he(x:Fin m): (soak x (a::l)).length=(soak x l).length+if x=a.1 then 1 else 0:= by by_cases h:x=a.1 <;> simp [h,Ne.symm,soak]
      simp_rw [he];rw [Finset.sum_add_distrib,ih];simp
lemma soak_head (a:Fin m)(l:List (Fin m × Axis)) : (soak a l).length ≤ l.length:= by rw [← soak_pile l]; exact Finset.single_le_sum (f:=fun i=> (soak i l).length) (fun i _=>Nat.zero_le _) (Finset.mem_univ a)
lemma office (S: Fin m→Cross L I J)(t: Cover)(a:chain I m)(l: List (Fin m × Axis))(h: Odd L.val): gang (crown S t a) l = crown (fun i=>advanceC L (S i) (soak i l)) t a:= by
   induction l with
   | nil=>rfl
   | cons v l ih=> rw [gang,ih,crown_foot _ _ _ v.1 v.2 h]; refine congr_arg (fun x=> crown x t a) ?_;ext1 i; by_cases he:i=v.1 <;> simp [he,Ne.symm, soak,advanceC]

lemma throne {A : Type*} (D:Reach A)(a:A)(v:chain A m) : wide D (Fin.cons a v : chain A (m+1))≤ ∑ j,D.d (v j) a:= by
    apply known_wide;intro i j; have hh i : D.d (v i) a≤∑ j,D.d (v j) a:= Finset.single_le_sum (f:=fun j=> D.d (v j) a) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)
    cases i using Fin.cases with
    | zero=> cases j using Fin.cases with
      | zero=> rw [D.self];exact Nat.zero_le _
      | succ j=> rw [D.turn];exact hh j
    | succ i=> cases j using Fin.cases with
      | zero=>exact hh i
      | succ j=>
          by_cases h:i=j
          · subst j;rw [D.self];exact Nat.zero_le _
          refine (D.tri (v i) a (v j)).trans ?_ ; rw [D.turn a,←Finset.sum_pair h (f:=fun i=>D.d (v i) a)]
          exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
variable [Fintype I][Fintype J]

lemma knobs (h:0≤η)(x:Biglot I)(t: chain I m)(u : Biglot J) (k:ℕ)(S: Fin m → Cross L I J)(C:Fin m→ℝ)(hC:∀ i,0≤C i)(hp:∀ i, Row.strip (S i) η (C i))(w:cloud m)(hw:size w≤k): Knoxville (fame _) η (piz L x u.2) (crown S x.1 t w) (∏ i: Fin m, Real.exp (η*(k/(L.val:ℝ)+8))*(Fintype.card J*C i)):= by
    let X i:= snake x.1 t w i; let y:=piz L x u.2; let D:= fame J; let E (i: Fin m):= Real.exp (η*(k/(L.val:ℝ)+8))*(Fintype.card J*C i)
    have hE (i: Fin m) : 0≤E i := by have hv:= hC i; unfold E; positivity
    refine ⟨Finset.prod_nonneg fun i _=>hE i,?_⟩
    let f (i: Fin m) (v:Biglot J):= Gorge.shine η (D.d v y)* ‖merit (S i) (X i) v‖ₑ
    have hh (v:chain (Biglot J) m): Gorge.shine η (wide D (Fin.cons y v : chain (Biglot J) (m+1))) * ‖crown S x.1 t w v‖ₑ ≤ ∏ i,f i (v i) := by
       refine (mul_le_mul_left (shine_le η h (throne D y v)) _).trans_eq ?_
       have enorm_prod (S : Finset (Fin m)) (x:Fin m→ℝ) : ‖∏ j∈S,x j‖ₑ = ∏ j∈S,‖x j‖ₑ:= by induction S using Finset.induction <;> simp_all [enorm_mul]
       rw [crown]; unfold f Gorge.shine X; simp only [Nat.cast_sum,Finset.mul_sum,Real.exp_sum]; rw [ENNReal.ofReal_prod_of_nonneg (fun _ _=>(Real.exp_pos _).le),enorm_prod, Finset.prod_mul_distrib]
    refine (ENNReal.tsum_le_tsum hh).trans ?_; rw [eun_tsum f, ENNReal.ofReal_prod_of_nonneg (fun (i: Fin m) _=>hE i)]; apply Finset.prod_le_prod'
    intro i _; apply tilt_path (X i) x u k _ _ (hp i) (hC i) h
    have he:=atom_size w i; apply le_trans _ (he.trans hw); unfold X capD snake; dsimp only; rw [show x.1-(x.1+_)= -(rack w i) by abel, size_neg]
-- width/moment bound before L

def gold (J : Type) [Fintype J](L:Side)(h k:ℕ)(b C :ℝ) := (Real.exp (b*(k/(L.val:ℝ)+8))*((Fintype.card J:ℝ)*C))^h * (L.val:ℝ)⁻¹^h
def gauss (S:Cross L I J)(η C : ℝ)(d:ℕ):= ∀ l:List Axis, l.length≤d → (advanceC L S l).strip η (C*(L.val:ℝ)⁻¹^(1+l.length))

lemma glutton (h:0≤η)(hc:0≤C)(S:Cross L I J)(d:ℕ)(H:gauss S η C d)(ho: Odd L.val)(x:Biglot I)(t:chain I m)(k:ℕ)(u : Biglot J)(l:List (Fin m × Axis))(hl:l.length≤d)(w:cloud m)(hw:size w≤k): Knoxville (fame _) η (piz L x u.2) (gang (crown (fun _=>S) x.1 t) l w) (gold J L m k η C*(L.val:ℝ)⁻¹^l.length):= by
   rw [office (fun _=>S) _ _ l ho]
   let B i := C*(L.val:ℝ)⁻¹^(1+(soak i l).length)
   apply (knobs h x t u k _ B (fun _=> by unfold B;positivity) (fun i=> H (soak i l) ((soak_head i l).trans hl)) w hw).mono; apply le_of_eq;
   unfold gold B; simp_rw [←mul_assoc];rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
   rw [Finset.prod_pow_eq_pow_sum, Finset.sum_add_distrib,soak_pile]; simp;ring
end YM.FormalBulk08.Chapel

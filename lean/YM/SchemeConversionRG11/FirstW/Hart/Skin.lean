import YM.SchemeConversionRG11.FirstW.Hart.Chart
/-! Native Ward subspaces (open legs). No ghosts/field quotients from this harmonic condition outside tree applications. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.FirstW
open Function Lattice Pert Align Topology Maxwell Filter
open scoped BigOperators Classical
variable {G : Gauge} {X : Type*} [One X] [AddCommGroup X] {k d : ℕ}
abbrev Field4 (G : Gauge):=Wind G ℤ
def field4 (i : Axis) (f : Wind G X) (x : Four X):= f (x,i)
def post (i : Axis) : Field4 G →ₗ[ℝ] (Cover→G.Color) where
 toFun := field4 i
 map_add' _ _:=rfl
 map_smul' _ _:=rfl
def stor (G : Gauge) (k : ℕ) : Submodule ℝ (Field4 G) := ⨅ i:Axis,(Loft G.Color k).comap (post i)
def atoneLap {V : Type*} [AddCommGroup V] (f : Four X→V) (x : Four X) := ∑ i:Axis, (f (x+step i)+f (x-step i)-2 • f x)
def atoneDiv (f : Wind G X) (x : Four X) := ∑ i:Axis,(f (x,i)-f (x-step i,i))
lemma stor_mem {p:Field4 G} : p∈stor G k ↔ ∀ i,field4 i p∈Loft G.Color k := by simp only [stor, Submodule.mem_iInf,Submodule.mem_comap];rfl
def cabin (G : Gauge) (k : ℕ) : Submodule ℝ (Field4 G) where
 carrier := setOf fun p=> p ∈ stor G k ∧ (∀ i:Axis,atoneLap (field4 i p)=0) ∧ atoneDiv p=0
 add_mem' {p q} h e:= by
   refine ⟨Submodule.add_mem _ h.1 e.1,fun i=>?_,?_⟩
   · funext x; have hp := congrFun (h.2.1 i) x; have he:= congrFun (e.2.1 i) x; have hh := congrArg₂ (·+·) hp he; unfold atoneLap at *; simp only [Pi.zero_apply,add_zero,←Finset.sum_add_distrib] at hh
     rw [Pi.zero_apply,← hh]; refine Finset.sum_congr rfl fun i _=>?_; dsimp only [field4,Pi.add_apply]; abel
   funext i; have he:=congrArg₂ (·+·) (congrFun h.2.2 i) (congrFun e.2.2 i); unfold atoneDiv at *; simpa only [Pi.zero_apply,add_zero, Pi.add_apply,add_sub_add_comm, Finset.sum_add_distrib] using he
 smul_mem' a p h:= by
   refine ⟨Submodule.smul_mem _ a h.1,fun i=>?_,?_⟩
   · have hp x:=congrFun (h.2.1 i) x; funext x; unfold atoneLap; simp only [field4,Pi.smul_apply,←smul_add, ← smul_comm a (2:ℕ), ←smul_sub, ←Finset.smul_sum]; change a • (atoneLap (field4 i p) x)=0; rw [hp]; exact smul_zero _
   funext i; simp only [atoneDiv,Pi.smul_apply,←smul_sub,← Finset.smul_sum]; change a • (atoneDiv p i) = 0; rw [show _=(0:G.Color) from congrFun h.2.2 i,smul_zero]
 zero_mem':=⟨Submodule.zero_mem _,fun i=>funext fun x=>by simp [atoneLap, field4],funext fun x=>by simp [atoneDiv]⟩
abbrev Home4 (G : Gauge) := cabin G
abbrev Nu (G : Gauge) (k : ℕ) := ↥(cabin G k)
def buzz (G : Gauge) (k : ℕ) : Submodule ℝ (Field4 G) := (cabin G k) ⊓ LinearMap.ker (LinearMap.pi (fun a : Axis=>LinearMap.pi fun b:Axis=>LinearMap.pi (fun x:Cover=> rail x (square a b))))
def quietly (A : Field4 G) := ∀ i j x, Bare.wideCurl A x i j=0
lemma hums {p:Field4 G} : p ∈ buzz G k ↔ p∈cabin G k ∧ quietly p := by
  simp only [buzz,Submodule.mem_inf,LinearMap.mem_ker,and_congr_right_iff]; intro hw
  exact ⟨fun h i j x=> by rw [←frontRail]; exact congrFun (congrFun (congrFun h i) j) x |>.trans (by rfl),fun h=>funext fun i=>funext fun j=>funext fun x=>by simp [frontRail,h i j x]⟩
lemma cabin_floor {p:Field4 G} (h:p∈cabin G k) (i : Axis): field4 i p∈ Loft _ k := stor_mem.mp h.1 i
lemma cabin_lap {p:Field4 G} (h:p∈cabin G k) (i : Axis): atoneLap (field4 i p)=0:= h.2.1 i
lemma cabin_div {p:Field4 G} (h:p∈cabin G k): atoneDiv p=0 := h.2.2
def lativ (k : ℕ) : stor G k →ₗ[ℝ] (Axis → Loft G.Color k) := LinearMap.pi (fun i=> LinearMap.codRestrict (Loft G.Color k) ((post i) ∘ₗ (stor G k).subtype) fun p=> stor_mem.mp p.property i)
instance : FiniteDimensional ℝ (stor G k):= FiniteDimensional.of_injective (lativ k) (fun p q h=> Subtype.ext (funext fun x=> by have hU:=congrFun h x.2; exact congrFun (congrArg Subtype.val hU) x.1))
lemma stepped_stor (h : k≤d) : stor G k ≤ stor G d := fun _ ha=> stor_mem.mpr fun i=>loft_mono h (stor_mem.mp ha i)
lemma stepped (h : k≤d) : cabin G k ≤ cabin G d := fun _ ha=>⟨ stepped_stor h ha.1,ha.2⟩
lemma cabin_stor : cabin G k ≤ stor G k := fun _ h=> h.1
instance : FiniteDimensional ℝ (cabin G k):= FiniteDimensional.of_injective (Submodule.inclusion cabin_stor) (Submodule.inclusion_injective _)
lemma shade_loft {V F : Type*} [NormedAddCommGroup V] [NormedAddCommGroup F] [NormedSpace ℝ V] [NormedSpace ℝ F] {f : Cover→V} (h : f∈Loft V k) (L : V→ₗ[ℝ] F): L ∘ f ∈ Loft F k := by intro D hD; exact (combine_map D L.toAddMonoidHom f).trans (funext fun x=>by rw [h D hD]; exact L.map_zero)
lemma preserving_color (u : G.El) (p : Field4 G) (he:p∈cabin G k): putting u p ∈ cabin G k := by
  refine ⟨stor_mem.mpr fun i=> shade_loft (cabin_floor he i) (G.adjoint u),fun i=>?_,?_⟩
  · funext x; have H:=cabin_lap he i; have hp:=congrArg (G.adjoint u) (congrFun H x); unfold atoneLap at *; simp_rw [map_sum,map_sub,map_add,map_nsmul,Pi.zero_apply,map_zero] at hp; exact hp
  funext x; have h:=congrArg (G.adjoint u) (congrFun he.2.2 x); unfold atoneDiv at *; simp_rw [map_sum,map_sub,Pi.zero_apply,map_zero] at h; exact h
end YM.RG11.FirstW

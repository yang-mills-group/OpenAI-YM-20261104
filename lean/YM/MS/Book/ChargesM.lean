import YM.MS.Book.Merit

/-!
# Intertwining algebra for allowed reparametrizations

Requires symplectic on q, q⁺ pairs inside ∆. No antisym anomaly.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Book.Program
open Function Filter Set Finset Koszul Plane Cylinder Lab Convolve Native Lattice
open PowerSeries (coeff)
variable {A B I : Type} (V:A→Cn) {p:Sector A}[Fintype I](B:Bonded p I) (hv:∀ i,V (B.plain i)*V (B.dual i)=1)
    {F H: T (Seed A Cover ℂ)} {x: Cn} (hx: Rooted x)

include hv
lemma car_mut (h:Mut B F) : Mut B (dotD V F):= by
   rw [whorled]; intro k; let U (n:Side) : Mode A (Site n) → Cn:= V ∘ Prod.fst
   let X (n:Side) := promote (docket n) F; let X0 (n:Side) := tokM B.district (X n)
   filter_upwards [(Finset.eventually_all (Finset.Iic k)).mpr (fun i _=> (whorled ..|>.mp h) i)] with n hn;
   have he i (hi:i≤k): X0 n i=0:= hn _ (Finset.mem_Iic.mpr hi)
   change tokM B.district (promote (docket n) _) k=_; rw [show promote (docket n) (dotD V F)= taxi (U n) (X n) from grid F V true n,tokensT (U n) (B.district (P:= Site n)) _ (fun i=> hv i.1)]; unfold taxi; simp only [LinearMap.coe_mk, AddHom.coe_mk]; exact Finset.sum_eq_zero fun i hi=> by change merit _ _ (X0 n i.2)=_; rw [he i.2 (by obtain ht := mem_antidiagonal.mp hi; omega),map_zero]
lemma car_steady : steadyE B (dotD V F) (dotD V H)= dotD V (steadyE B F H):= by
    let X (n:Side):= V ∘ (Prod.fst: Mode A (Site n)→ _)
    funext k; rw [← enterEq ..]; filter_upwards [(Finset.eventually_all (Finset.Iic k)).mpr (fun i _=> read_dual (k:=i) (B:=B) F H false),read_dual (k:=k) (B:=B) (dotD V F) (dotD V H) false] with n hn hv'
    let W:=promote (docket n) F; let Y:=promote (enters n) H; let Q:=promote (enters n) (steadyE B F H)
    have h' i (hx:i≤k): Q i= modulo B.district W Y i:= hn _ (Finset.mem_Iic.mpr hx)
    change duty false n _ = promote (duty false n) (dotD V _) k; rw [hv',grid,grid]; rw [show promote (docket n) (dotD V F)=taxi (X n) W from grid F V true n, show modulo B.district (taxi (X n) W) (taxi (V ∘ (Prod.fst:Mode A (Site n)→ _)) (promote (duty false n) H))=taxi (X n) (modulo B.district W Y) from ?hb]; swap
    · change modulo B.district (taxi (X n) W) (taxi (X n) Y)=_; unfold modulo; simp_rw [LinearMap.add_apply,map_add,meterz (X n) B.district Y (fun i:I×Site n=> hv i.1),meterr (X n) B.district W Y (fun i:I×Site n=> hv i.1)]
    change (taxi (X n) (modulo B.district W Y) k)=(taxi (X n) Q k); unfold taxi; simp only [LinearMap.coe_mk, AddHom.coe_mk]; refine Finset.sum_congr rfl (fun i hi=> ?_); change _=merit _ _ (Q i.2); rw [h' i.2 (by obtain ht:= mem_antidiagonal.mp hi; omega)]
lemma car_Weight (h:Weightless B F H): Weightless B (dotD V F) (dotD V H):= by unfold Weightless; rw [car_steady V B hv,h,dotD,map_zero]
omit hv
include hx
lemma subMut (h:Mut B F): Mut B (substitute x F):= by
   unfold Mut; intro k; have he : masterE B (substitute x F)=substitute x (masterE B F):= by
       change actB _ _ +_ =_; rw [show masterE B F=actB B F+_ from rfl,map_add,map_smul]; unfold blocks actB; rw [comm,substitute_pair hx]
   rw [he,rules]; filter_upwards [(Finset.eventually_all (Finset.Iic k)).mpr (fun i _=> h i)] with n hn; rw [map_sum,map_zero]; refine Finset.sum_eq_zero fun j hj=>?_ ; rw [map_smul,hn j hj,map_zero,smul_zero]
lemma subWeight (h:Weightless B F H): Weightless B (substitute x F) (substitute x H):= by
    change promote B.Lap (substitute x H)+pairW _ _ _=0
    rw [comm,substitute_pair hx, ← map_add,show promote B.Lap H +pairW B.touch F H = 0 from h,map_zero]
lemma modSub : steadyE B (substitute x F) (substitute x H) = substitute x (steadyE B F H):= by
    change promote B.Lap (substitute x H) + pairW B.touch _ _= substitute x (promote B.Lap H+pairW B.touch F H); rw [map_add,comm,substitute_pair hx]
end YM.MS.Book.Program

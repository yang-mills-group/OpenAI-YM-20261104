import YM.OPE.Compatible.Vines.Icing
/-! Taylor gradients through shafts decomposition. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free Maxwell Labels Tensor ContinuousMultilinearMap WithLp
open scoped Topology BigOperators Classical
variable {r d m n:ℕ}{c:ℝ}{T I:Type*}
namespace Script
open Page
private lemma shiftP (x:E4)(l:List Axis)(i:Axis):
   let v := tasting l; let f (t:Lieu Axis):= t i
   gust x (tasting (i::l))-breeze x (tasting (i::l))=f*(gust x v-breeze x v)+(x i) • gust x v:=by
      intro v f; ext t; let h := v ∘ invertX; let y:=compAxis i; have he:= (jig (flavor_part l l.length le_rfl) (fromX t)).hasFDerivAt
      have ht:= ((y.hasFDerivAt (x:=fromX t)).mul he).fderiv
      change _- (fderiv ℝ (tasting (i::l) ∘ invertX) (fromX t)) x=_
      rw [show tasting (i::l) ∘ invertX=(y: E4→ℝ)*h from rfl,ht]
      change (t i + x i)*v _ - t i*v t - (t i*breeze x v t + v t * x i) = t i * (gust x v t-breeze x v t)+x i*gust x v t; unfold gust; ring
lemma tailP (f:Lieu Axis→ℝ)(h:f∈Flavor Axis d)(x:E4): gust x f-breeze x f∈Flavor Axis (d-2)∧ (d<2→gust x f=breeze x f):=by
    let K:= Flavor Axis (d-2)
    suffices hh : gust x f-breeze x f∈K∧ (d<2→gust x f-breeze x f=0) from ⟨hh.1,fun hi=>sub_eq_zero.mp (hh.2 hi)⟩
    refine flavor_elim h (fun f=> gust x f-breeze x f∈K∧ (d<2→gust x f-breeze x f=0)) (fun i hi=>?_) ?_ ?_ ?_
    · have h(i:List Axis): gust x (tasting i)-breeze x (tasting i) ∈ Flavor Axis (i.length-2)∧ (i.length<2→gust x (tasting i)-breeze x (tasting i)=0):=by
         clear hi; induction i with
         | nil=> have he: gust x (tasting [])-breeze x (tasting [])=0:=by ext; simp [gust,tasting,breeze,Function.comp_def]
                 rw [he]; exact ⟨(Flavor Axis _).zero_mem,fun _=>rfl⟩
         | cons i l ih=>
           rw [shiftP,List.length_cons, Nat.succ_sub_succ_eq_sub]; let g(t:Lieu Axis):=t i; have he:= sudden (tasting l) (flavor_part l l.length le_rfl) x; by_cases hh:l.length<2
           · rw [ih.2 hh,mul_zero,zero_add]; exact ⟨(Flavor Axis _).smul_mem _ he.1,fun h=> by rw [he.2 (by omega), smul_zero]⟩
           exact ⟨(Flavor Axis _).add_mem (flavor_up (by omega) (flavor_prod (flavor_position i) ih.1)) ((Flavor Axis _).smul_mem _ he.1), by omega⟩
      exact ⟨flavor_up (by omega) (h i).1,fun he=>(h i).2 (hi.trans_lt he)⟩
    · rw [gust_zero,show breeze x 0=0 from funext fun i=>by simp [breeze,Function.comp_def],sub_zero]; exact ⟨K.zero_mem,fun _=>rfl⟩
    · rintro v w hv hw ⟨hx,h⟩ ⟨hz,g⟩; rw [show gust x (v+w)=gust x v+gust x w from funext fun i=>by simp [gust]; abel, show breeze x (v+w)=breeze x v+breeze x w from funext fun i=>by
            unfold breeze; rw [show (v+w) ∘ invertX = v∘invertX+w∘invertX from rfl, fderiv_add (jig hv _) (jig hw _)]; rfl, add_sub_add_comm]; exact ⟨K.add_mem hx hz,fun i=>by rw [g i,h i, zero_add]⟩
    rintro k v hv ⟨hx,g⟩; rw [show gust x (k • v)=k • gust x v from funext fun i=>by simp [gust,mul_sub], show breeze x (k • v)= k • breeze x v from funext fun i=> by
          unfold breeze; rw [show (k • v) ∘ invertX= k • (v ∘ invertX) from rfl, fderiv_const_smul (jig hv _)]; rfl, ← smul_sub]; exact ⟨K.smul_mem k hx,fun i=> by rw [g i,smul_zero]⟩
end Script
end YM.OPE.Flume

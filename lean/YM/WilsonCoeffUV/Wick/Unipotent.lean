import YM.WilsonCoeffUV.Wick.Intertwiner
/-!
# Unipotence of Wick coupling frame. Pivot nondegeneracy not asserted. Exact filters match through G-S.
-/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil
open Exterior Next.Free Tree Precision Power Embroider Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm Fountain
open Bank.Carp
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {c f n:Side}{U V α:Type*} {G:Gauge} {h D i j k e n' m N r:ℕ}{F:Labels.Frame G h} {H:Hol G}
variable {z ξ σ A' B:ℝ} {s t:ℝ}
variable {A:Levels G}{Ñ:ChartRatio G}{I:Cloister G h}{J:Usage A Ñ m}
lemma identT {A B:Wall F}(p:Tram F 0 A)(q:Tram F 0 B): identum (A*B)=identum A*identum B:=by
    ext i j; unfold identum; rw [Matrix.of_apply,Matrix.mul_apply]; split
    next hv=> rw [Matrix.mul_apply]; refine Finset.sum_congr rfl fun v hv' =>?_ ;
              simp only [Matrix.of_apply,hv]; rcases lt_trichotomy (valence F v) (valence F j) with h|h|h
              · rw [p _ _ (by omega), if_neg (by omega),zero_mul,zero_mul]
              · rw [if_pos h.symm,if_pos h]
              rw [q _ _ (by omega),if_neg (by omega),if_neg (by omega)]; simp
    next hp=> symm; exact Finset.sum_eq_zero (fun i _=>by simp only [Matrix.of_apply]; split_ifs <;> first|omega|simp)
lemma ident_lease {A:Wall F}(p:leaseM n F A): leaseM n F (identum A):=by refine ⟨fun i j v=> if_neg (by omega),fun i j u v=>?_⟩; unfold identum; rw [Matrix.of_apply,if_pos u,p.2 i j u v]
lemma ident0 :identum (1:Wall F)=1:=by ext i j; by_cases h:i=j; subst j; simp [identum]; simp only [identum,Matrix.of_apply,Matrix.one_apply_ne h,ite_self]

lemma maCap (P:Gen (Vote D) (YForest G))(h:still P (r+1))(x N m:ℕ): paveS A m N x P r=P r:=by
    unfold paveS mason; rw [Finset.sum_apply, Finset.sum_eq_single_of_mem 0]; rfl
    · simp
    intro j h' hp; exact ice_none h (by omega)
lemma wick_stand (X: Island F D)(p:Shimmer X)(m N:ℕ): leaseM 1 F (wickM A m N F X.2):=by
   let M:=wickM A m N F X.2
   have he i : still (X.2 i 0) (valence F i+1):= fun j hj=> (streams p i).born 0 j (by omega)
   refine ⟨fun i j v=>?_,fun i j v _=>?_ ⟩
   · unfold wickM wickT; rw [Matrix.of_apply,show paveS A m N h _ _=0 from mason_cap _ (he _) (valence F i) (by omega),echo_zero]
   unfold wickM wickT; rw [Matrix.of_apply, v,maCap _ (he _), ← v,← g_lone, epoch p]; by_cases h:i=j; · simp [matPow,h]
   simp [h,Ne.symm h]
lemma wick_unit (X:Island F D)(p:Shimmer X)(N m:ℕ): IsUnit (wickM A m N F X.2).det:= trove (wick_stand X p m N)
lemma household {P:Wall F}(i j: Alma F)(p:leaseM n F P)(hp: h=weight F j): identum P i j=(1:Wall F) i j:= by
   unfold identum; rw [Matrix.of_apply,Matrix.one_apply]; split
   next u=> rw [p.2 i j u (by have hh:= weigh_cap F i; omega)]; simp [matPow,hp]
   next u=> rw [if_neg (fun (z:i=j)=>u (congr_arg (valence F) z))]

open PowerSeries
section inner
variable {T:SectionData F}{p:h<D}{E W:Credit}(L:Theatre H T p e E W)
abbrev Wray (A:Levels G)(Ñ:ChartRatio G)(T:SectionData F)(p:h<D)(N m:ℕ): Wall F:= wickM A m N F (Peaks A Ñ T p N m).2
abbrev forwardW (A:Levels G)(Ñ:ChartRatio G)(T:SectionData F)(p:h<D)(N m k:ℕ): Wall F:= lineS (CurNames A Ñ T p N m k false) 0
lemma junior : lineS (1:Coil F) 0=1:=by rw [line0,map_one]
lemma fPace (A:Levels G)(Ñ:ChartRatio G)(T:SectionData F)(p:h<D)(N m k:ℕ): forwardW A Ñ T p N m (k+1)=lineS (Jacob A Ñ T p N m) 0 *forwardW A Ñ T p N (m+1) k:= by
    unfold forwardW; rw [roll1,line_mul,Finset.Nat.antidiagonal_zero,Finset.sum_singleton,maxStroke]
lemma wallways (a:L.V.anchor≤m)(w:m+k≤N): let P:=forwardW L.V.draws L.V.paid T p N m k; let M j:=Wray L.V.draws L.V.paid T p N j; M m*P=identum P*M (m+k)∧ Tram F 0 P ∧ IsUnit (P.det) ∧ ∀ i j,h=weight F j → identum P i j=(1:Wall F) i j:=by
    let R m k:= forwardW L.V.draws L.V.paid T p N m k
    let V m:= Wray L.V.draws L.V.paid T p N m
    induction k generalizing m with
    | zero=>
       intro W V; have hp: W=1:=by unfold W forwardW CurNames; rw [hillcrest]; exact junior
       rw [hp,ident0]; exact ⟨by simp,Tram.one,by simp,fun _ _ _=>rfl⟩
    | succ k ih=>
       intro P W'; let Q:= Jacob L.V.draws L.V.paid T p N m; let Z:=lineS Q 0
       let B:= R (m+1) k; have hv: m+(k+1)= (m+1)+k:=by omega
       have hf:P= Z*B:= fPace ..; rw [hf]; obtain ⟨x,y,z,c⟩:= ih (show L.V.anchor≤m+1 by omega) (by omega); have heZ:=leaseN L (N:=N) a (by omega); have h:Tram F 0 Z:=heZ.1; rw [identT h y,hv]; refine ⟨?_,h.mul y,by rw [Matrix.det_mul]; exact (trove heZ).mul z,?_⟩
       · change W' m * (Z * R (m+1) k) = identum Z * identum B * _; rw [← Matrix.mul_assoc, show _ * Z= _ from intercore L a (show m<N from by omega), Matrix.mul_assoc,show V (m+1)* R (m+1) k=_ from x,Matrix.mul_assoc]
       intro i j t; rw [Matrix.mul_apply]; change (∑ x,identum Z i x * identum (R (m+1) k) x j)=(1:Wall F) i j; simp_rw [show ∀ x,identum (R (m+1) k) x j= _ from fun x=>c x j t]; rw [← Matrix.mul_apply,Matrix.mul_one]; exact household i j heZ t
lemma top_ray (a:L.V.anchor≤m)(w:m+k=N)(j: Alma F)(H:h=weight F j):
    ((forwardW L.V.draws L.V.paid T p N m k)⁻¹*(Wray L.V.draws L.V.paid T p N m)⁻¹) *ᵥ (Pi.single j 1) = (Wray L.V.draws L.V.paid T p N N)⁻¹ *ᵥ Pi.single j 1:=by
    subst N; obtain ⟨x,y,z,c⟩:=wallways L a (le_refl (m+k)); let P:= Wray L.V.draws L.V.paid T p (m+k) m; let Q:= Wray L.V.draws L.V.paid T p (m+k) (m+k); let V:=forwardW L.V.draws L.V.paid T p (m+k) m k; let t:= Pi.single (M:=fun _=> ℝ) j 1; have hp: IsUnit P.det:= wick_unit _ (production L (by omega) a).1 _ _; have hq: IsUnit Q.det:=wick_unit _ (production L le_rfl (by omega)).1 _ _; have hv:P*V=identum V*Q:=x; have hh:identum V*ᵥ t=t:= by funext i; unfold t; rw [Matrix.mulVec_single_one (identum V) j]; exact (c i j H).trans (by simp [Matrix.one_apply, Pi.single_apply])
    apply (show Injective (Matrix.mulVec (P*V)) from Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr (by rw [Matrix.det_mul]; exact hp.mul z)))
    change (P*V)*ᵥ ((V⁻¹*P⁻¹)*ᵥt)=(P*V)*ᵥ(Q⁻¹*ᵥt); rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,hv]; rw [← hv,← Matrix.mul_assoc,Matrix.mul_assoc P,Matrix.mul_nonsing_inv V z, _root_.mul_one, Matrix.mul_nonsing_inv P hp, Matrix.one_mulVec,hv, Matrix.mul_assoc,Matrix.mul_nonsing_inv Q hq,_root_.mul_one]; exact hh.symm
end inner
end YM.WilsonCoeffUV.Cosmos

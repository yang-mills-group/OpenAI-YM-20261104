import YM.WilsonCoeffUV.Marked.Paths.SpineCover
/-!
# The form of the Ward saving needed for successive grade lifting
 On aggregated potential series. Independent of their release presentation.
 Full `climes` supply includes analytic root widths through finite height.
 Preserve upon changing tree path lifts (priced alternate completions with
 same leading coefficients or arbitrary forecast through LOWER heights). No
 claim changing two actual E presentations. -/
set_option autoImplicit false
set_option maxHeartbeats 550000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Rolls
open Gauge Power PowerSeries Matrix Filter Lattice Laurent Exterior Precision Wilson RG Tree Bloch Stationary
open Function Blue Bank Fountain Soil Source Source.Drops Labels Cosmos Planned.PrimaryIntegral295 Place Carrier Bank.Carp Bank.Mosaic Bank.Mosaic.Near
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{n:Side}{k h r t i j e:ℕ}{s u A B:ℝ}
variable {V W I α β:Type}[NormedAddCommGroup V][NormedSpace ℝ V]

-- germ conditions finite bound true horizon **exclusive**
structure Nimbus (k e:ℕ) (P:Bookend V G) : Prop where
    lead i : i< e → Pure (P i)
    shell i : i< e→ still (P i) (k+i+1)
    vert i : i< e→ pillar P i
    hue i : i< e →∀ j,mural (P i j)
lemma nimb (P:Era G V)(p:Auth k P)(e:ℕ) : Nimbus k e P.2:= ⟨fun _ _=>p.coverP _, fun i _ j h=>p.coverN i j h,fun _ _=>pagoda p _,fun i _=>pigment p i⟩
variable {F T:Bookend V G}
lemma marbles {P Q: Ten V (YForest G) r}(p:mural P)(q:mural Q): mural (P-Q):=by
   intro x v y; rw [Pi.sub_apply,p x v y,q x v y,←Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _; rw [←smul_sub]; rfl
lemma wick_zero (b:G.Color)(c:G.Color)(x:Edge Cover)(j:G.ColorIndex)(i:ℕ) : wickLamp b c x j i (0:Gen V (YForest G)) = 0:=by
    have he:= floatT (0:Gen V (YForest G)) b c x i j 0; rw [sub_self,sub_self] at he; exact he
lemma twilit (p:Nimbus k e T)(h:Nimbus k e F): Nimbus k e (T-F):=by
    refine ⟨fun i t j q x=>congr_arg₂ (·-·) (p.lead _ t j q x) (h.lead _ t j q x),fun i t j x=>by simp only [Pi.sub_apply,p.shell _ t j x,h.shell _ t j x,sub_zero],fun i v b x=>?_,fun i t j=>marbles (p.hue _ t _) (h.hue _ t _)⟩
    dsimp only [Pi.sub_apply]; simp_rw [floatT,show ∀ a b c d: Gen V (YForest G), (a-b)+(c-d)= a+c-(b+d) from fun a b c d=>by abel, Finset.sum_sub_distrib,p.vert _ v b x,h.vert _ v b x]; exact sub_self _
lemma nymph (p:Nimbus k e T)(q:i<e)(u:∀ j< i,T j=0): ∀ j (v:r=j+1),∀ x c,windsL (r:=j) x c (v ▸ T i r)=0:=by
    rintro R rfl x c
    let b:=coatC G (Pi.single c 1); have hz (j:ℕ×ℕ)(h:j ∈ (Finset.antidiagonal i).erase (0,i)) (v:Axis)(w:G.ColorIndex): wickLamp b 0 (x,v) w j.1 (T j.2)+ wickLamp 0 b (x-step v,v) w j.1 (T j.2)=0:=by
       obtain ⟨H,P⟩:= Finset.mem_erase.mp h; have hv:j.1+j.2=i:=Finset.mem_antidiagonal.mp P; have hh:j.2≠i:=fun e=> H (Prod.ext (by omega) e); rw [u _ (by omega), wick_zero,wick_zero,add_zero]
    have he : northL 0 x b (T i)=0:=by
       rw [← p.vert _ q b x]; unfold northL; apply Finset.sum_congr rfl; intro v _; apply Finset.sum_congr rfl; intro a _; rw [Finset.sum_eq_single (0,i)]
       · intro j hj z; exact hz j (Finset.mem_erase.mpr ⟨z,hj⟩) v a
       simp
    have hp:= wick_winds x c (T i) (p.lead i q) R; change northL _ _ b _ R=_ at hp; rw [he] at hp; have h': (R+1) • windsL x c (T i (R+1))=0:=hp.symm
    rw [← Nat.cast_smul_eq_nsmul ℝ] at h'; exact (smul_eq_zero.mp h').resolve_left (by positivity)

-- statements through period normalization rollTest require Nimbus pad below.
end YM.WilsonCoeffUV.Mer.Rolls

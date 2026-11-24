import YM.FormalBulk08.Kemp.Isle

/-! `W` → `T` Rite means W is T turned, so at root x of T use s-act x at W. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Kemp
open Reef Lava Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 PowerSeries Bank
open Stationary Lotus Shore Mesa Gorge City Cork Rift
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge} {n:Side} {I : Type} (x:Site n)

def resite (P : Pap (wire G n)) := PowerSeries.map (MvPolynomial.rename (Lotus.tint x)).toRingHom P
def work (x:Cover)(T: Pot G) : Pot G:= fun e r=> carries x (T e r)
lemma seated (x:Cover)(T:Pot G)(j : ℕ) (n:Side) (hm: Young T j) (h:∀ e r,Agate (T e r)): banner j (work x T) n=resite (wrap n x) (banner j T n):= by
    have he : Young (work x T) j := by intro a b ha; apply hm; intro he; unfold work at ha; rw [he] at ha; exact ha rfl
    ext1 e; let E:=e+j; let A:=banner j T n;
    rw [resite,coeff_map,banner,coeff_mk]; change _= MvPolynomial.rename _ (coeff e A); unfold A; rw [banner,coeff_mk,map_sum]; refine Finset.sum_congr rfl fun k hk=> ?_
    let L: Tile (wire G n) k:= sieve n (T e k); let f : Equiv.Perm (wire G n):=Lotus.tint (wrap n x);
    have hx : f.symm=Lotus.tint (-wrap n x) := by ext t <;>simp [f,Lotus.tint]
    rw [work,wears x n,hFac k f L]; swap
    · exact (sieve_sand _ _ (h e k))
    -- maybe names
    unfold carries; rw [hx]
where
    hFac (m:ℕ)(f:Equiv.Perm (wire G n))(K:Tile (wire G n) m)(hk : Agate K) : MvPolynomial.rename f (facade m K)=facade m (jetty f.symm K) := by
       have hp:= marble_grade m (MvPolynomial.rename f (facade m K)); rw [Shore.pebble,cores_once,marble_rec m K hk, MvPolynomial.homogeneousComponent_eq_self ((facade_grade _ _).rename_isHomogeneous)] at hp; exact hp.symm

lemma label_w [Fintype I] (A:Jets.Rays I→Jets.Rays (wire G n)) (hA:A 0=0)(h:ContDiffAt ℝ ω A 0) (T:Pap (wire G n)) : roam ℝ (motor A) (resite x T)=roam ℝ (motor (fun z=> A z ∘ Lotus.tint x)) T:= by
    unfold resite; let f:=fun v:Jets.Rays (wire G n)=> v ∘ Lotus.tint x
    rw [←fit_translate,roam_compose, show (fun i=>roam ℝ (motor A) (motor f i))=motor (f ∘ A) from (funext fun i=>motor_compose f A (contDiffAt_pi.mpr fun _=>contDiffAt_apply ..) (h.of_le le_top) rfl hA i)]
    rfl
lemma zooms (z: Jets.Rays (wire G n)): input G n (z ∘ tint x)= pull (1:Signed) x (input G n z):= by
    funext b; rw [pull_one];unfold input Lattice.translate; simp_rw [Work.F03.represent_link]; congr
lemma commute (a : Site n→G.El) (U : Config G n): pull 1 x (Lattice.gauge a U)= Lattice.gauge (fun z=>a (z+x)) (pull 1 x U):= by rw [pull_one,pull_one]; funext i; unfold Lattice.gauge Lattice.translate; change a _ *U _ *(a (i.1+x+step i.2))⁻¹ = a _*U _*(a (i.1+step i.2+x))⁻¹; rw [add_right_comm i.1]
lemma repulp (s : Signed) (W T: Pap (wire G n))(ht:Rite W T s 0): Rite (resite (s.act x) W) (resite x T) s 0:= by
    intro I i a b k ha hb hf hg hk hv hu
    rw [label_w _ a ha hf,label_w _ b hb hg]
    apply ht I (fun z=> a z∘ Lotus.tint (s.act x)) (fun z=> b z∘ Lotus.tint x) (fun z y=> k z (y+x)) (by rw [ha];rfl) (by rw [hb];rfl) (contDiffAt_pi.mpr fun j=> contDiffAt_pi.mp hf (Lotus.tint _ j)) (contDiffAt_pi.mpr fun j=> contDiffAt_pi.mp hg (Lotus.tint _ j)) (fun _=>hk _)
    · obtain ⟨g,h⟩:= hv; exact ⟨g,by rw [h]⟩
    filter_upwards [hu] with z hz; rw [zooms,zooms,hz,commute,pull_pull,pull_pull]; simp [affine]
end YM.FormalBulk08.Kemp

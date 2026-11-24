import YM.WilsonCoeffUV.FieldRead.TopRead
import YM.WilsonCoeffUV.Root.Step.Pivot
/-! # Copies of the same actual Section stencils, honoring even wraps. Log jets.
Not asserting used masks on full actual field definitions here. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n c:Side}{U V:Type*}{r h D l j e:ℕ} {G:Gauge}{F:Labels.Frame G h} (T:SectionData F) (w:h<D)
abbrev Estate (G:Gauge)(D):= (n:Side)→Vell G n D

def dockG (n:Side): Toe T→Woods G n:= foldUnder n ∘ dance T
def herald (v:Alma F): Estate G D:= fun n e r x=> fade (spear (dockG T n)) (sprig (collar T (sheet F v)) (valence F v) e) r x • jewelBloom w v
lemma herald_norm (v:Alma F)(n): shellK (valence F v) (herald T w v n):=by
   intro i j h; ext1 x; unfold herald; rw [show fade _ _ _=0 from fade_shell (spear (dockG T n)) (sprig_count (collar T (sheet F v)) (valence F v)) i j h]; exact zero_smul ..
lemma herald_auth (v:Alma F)(n i): Pure (herald T w v n i):=fun j q x=>by unfold herald; rw [fade_pure (sprig_pure (collar T _) (follicle ..) _ _) (spear (dockG T n)) j q]

lemma herald_job (v:Alma F)(e r): Bends 0 (fun n=> herald T w v n e r) (anthem T w v e r):=by
    classical
    let f:=sprig (collar T (sheet F v)) (valence F v) e; let Q:= jewelBloom w v
    let x:=dance T; let p:=fun n=> foldUnder n ∘ x
    have ht: anthem T w v e r = fun y=> fade (spear x) f r y • Q:=by
       by_cases h: valence F v+e=r; · subst r; rw [anthem,shine_lit]; rfl
       ext1 y; rw [anthem, shine_dark h]; unfold fade f sprig; simp only [shine_dark h,Pi.zero_apply]; simp
    let U (n:Side)(b:Fin r→ Toe T) (t:dock (Site n) (Hooks G) r):= if p n ∘ b=t then f r b • Q else 0
    let X (b:Fin r→Toe T)(z:Fin r→ YForest G) := if x ∘ b=z then f r b • Q else 0
    have hx {V:Type}(g:Toe T→V)(t:Fin r→V)[DecidableEq V]: fade (spear g) f r t • Q= ∑ b:Fin r→Toe T, if g ∘ b=t then f r b • Q else 0:=by
        rw [fade,Finset.sum_smul]; apply Finset.sum_congr rfl; intro b _; split
        next h'=> rw [←h']; simp [spear]
        next h'=> obtain ⟨i,hi⟩:=Function.ne_iff.mp h'; rw [Finset.prod_eq_zero (Finset.mem_univ i),zero_smul,zero_smul]; rw [spear,Matrix.of_apply,if_neg]; exact hi.symm
    have hT : anthem T w v e r=∑ b:Fin r→Toe T,X b:= by rw [ht]; ext1 y; rw [Finset.sum_apply]; convert! hx x y using 1
    have he b: Bends 0 (fun n=> U n b) (X b):=by
       let A:ℝ:= ‖f r b • Q‖ * Real.exp (port_d 0 (x ∘ b))
       have ha: 0≤A:=mul_nonneg (norm_nonneg _) (by positivity)
       refine ⟨fun y=>tendsto_const_nhds.congr' ?_,1,A,one_pos,(Soil.seen (p:=0) (x ∘ b)).mono fun n hn=>⟨ha,fun i=>?_⟩⟩
       · filter_upwards [eventually_all.mpr (fun i:Fin r=> fold_faith (x (b i)) (y i))] with n hn
         have hw : p n ∘ b=slideC n y ↔ x ∘ b=y:= ⟨fun q=>funext fun i=> (hn i).mp (congr_fun q i),fun q=>congr_arg (slideC n) q⟩
         unfold X U; simp only [hw]
       unfold U; split
       next h =>
          rw [←h,show tread (tor n) (wrap n 0) (p n ∘ b)= port_d 0 (x ∘ b) from hn,neg_one_mul,Real.exp_neg]; unfold A; rw [mul_assoc,mul_inv_cancel₀ (by positivity),mul_one]
       rw [norm_zero]; exact mul_nonneg ha (by positivity)
    rw [hT]; refine (Bends.sum (s:=Finset.univ) (fun b _=>he b)).congr (Eventually.of_forall fun n=>?_); ext1 d; simp_rw [Finset.sum_apply]; symm; convert! hx (p n) d using 1

lemma filtering_span (H:Hol G)(g:T.Sound H)(u:F.Index)(A:Lawn (Woods G n)): collar T u (spear (dockG T n)*ᵥ A)=(T.places (Pi.single u 1) 0 (mantle A)).re:=by
   change (Complex.ofReal (collar T u (spear (dockG T n)*ᵥ A))).re=_; rw [shawl T u H g,Source.SectionData.places]; apply congr_arg Complex.re; apply T.cylinder_local; intro i ht he
   obtain ⟨p,x⟩:= i
   let k:Spot T.stencil:= ⟨(⟨p,ht⟩,x), he⟩
   change pore _ (placeEdge k)=_; rw [pore_site, expandAt, bare_linkC]; congr 2; rw [spear_act]; ext j; simp only [add_zero]; rfl

abbrev Plies (T:SectionData F)(u:F.Index)(n:Side)(Y:Lawn (Woods G n)):= (T.places (Pi.single u 1) 0 (mantle Y)).re
lemma innu (H:Hol G)(g:T.Sound H)(u:F.Index)(n:Side): Green (Plies T u n):= by
   have he : Plies T u n=(collar T u) ∘ (fun z=> spear (dockG T n)*ᵥ z):= funext fun z=>(filtering_span T H g u z).symm
   rw [he]; apply ContDiffAt.comp _ _ (board _); rw [Matrix.mulVec_zero]; exact follicle T u
lemma herald_lit (v:Alma F)(n:Side)(c:Volume D)(p:Bid.pop T)(H:Hol G)(hq:T.Sound H):
    PowerSeries.X^valence F v * flash (jot c (herald T w v n))= jewelBloom w v c • jet (Plies T (sheet F v) n):=by
   let W:=spear (dockG T n); let f:= collar T (sheet F v); let K:=sprig f (valence F v); let B:= jewelBloom w v c
   have he : jot c (herald T w v n)= B • (fun i=> fade W (K i)):=by
       ext i r t; change (fade W (K i) r t • jewelBloom w v) c= B* _; rw [_root_.smul_apply,smul_eq_mul,mul_comm]
   have ht : valence F v= (F.grades (sheet F v)).2:= rfl
   let x:= valence F v
   have hu : PowerSeries.X^x* flash K= jet f := moves _ (fun i hi=>by rw [jet_apply,show rye f i=0 from wool T _ p hi,map_zero])
   have hh := congr_arg (loom W) hu
   rw [map_mul,map_pow,show loom W PowerSeries.X=PowerSeries.X from by simp [loom],loom_jet W f (follicle ..)] at hh
   rw [he,flash_mu (P:=fun i=> fade W (K i)) B (fade_shell W (sprig_count f (valence F v))), ←loom_fade W K (finite_shell (sprig_count f (valence F v))), mul_smul_comm]; change B • (PowerSeries.X^x * _)=_; rw [hh]; apply congr_arg (fun f:Lawn (Woods G n)→ℝ=>B • jet f); funext i; exact filtering_span T H hq _ _
end YM.WilsonCoeffUV.Cosmos

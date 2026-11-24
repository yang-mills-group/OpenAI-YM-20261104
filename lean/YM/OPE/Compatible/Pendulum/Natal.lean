import YM.OPE.Compatible.Pendulum.Judges
/-!
# leaf (normal) budgets, cove, peers. Leaf rates include *proper engineering*. Corrected lens phase powers exchange once, NOT once per ancestor.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Pixel
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset
open Push Marker Source Accent Ribbon Menu Local Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open PhysicalNext.Repeat.Legato Bandage
open Extra.Multi GridApprox.Nil Next.Rank
open Extra.Trajectories MergeProof.Float Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Stem
open Mirror Deb Allot Lights Wave Relay Cells CutOrder Arcade
open scoped Topology BigOperators Classical
variable {X I : Type} [PartialOrder X][OrderBot X][Fintype X](D:Origin X){U:Finset X}
   {G:Gauge}{C:Family G}{L:Extraction.Order}(A:Allot C)(hG:G.Simple){φ:Filter I}{s:I→X→ℝ}{T z c a r:I→ℝ}
    {q:I→ℕ}(b d:ℕ){η:ℝ} (h:Glowing D U φ T s η){W d' d₀:ℕ}(u:X)(hu:u∈U)
set_option quotPrecheck false
local notation "K"=> C.S.a
local notation "p"=>fun i=>aperture D C b d η (T i) (s i)
local notation "Y"=>fun i=>schedule C b η (s i)
local notation "j"=>fun i=> Y i u-1
variable (v:brim D U→ℕ) {w:I→brim D U→ℝ}
local notation "J"=> brim D U
local notation "Γ"=> cove D U u
local notation "Π!"=> univ \Γ
local notation "g"=>  fun i (x:brim D U)=> Run.Below C.path (w i x) (p i x.val) (finishAt D (Y i) x.val)
def area (v:brim D U→ℕ)(s:X→ℝ) (F:Finset (brim D U)):=∏ i∈ F,s (par D i.val)^v i
local notation "k₀"=>fun i=> area D v (s i) Γ
local notation "k₁"=>fun i=>area D v (s i) Π!
variable (hw : ∀ x:brim D U, Round φ T (fun i=> w i x/ s i (par D x.val)^(v x)))
include h
-- positivity at future
lemma area_pos (F:Finset J): ∀ᶠ i in φ,0< area D v (s i) F:=by
    filter_upwards [eventually_all.mpr (fun i:J=> (h.fade _ ((on_brim ..).mp i.2|>.2.2)).eventually self_mem_nhdsWithin)] with i hi; exact Finset.prod_pos fun j' _=> pow_pos (hi j') _
-- decomposition
omit h
lemma area_volume (s:X→ℝ): volume D U v s=area D v s (cove D U u)*area D v s (univ\cove D U u):=by simpa only [area,volume,univ_inter] using (prod_inter_mul_prod_sdiff univ (cove D U u) (fun x:brim D U=> s (par D x.val)^v x)).symm
include h hw hG A
lemma area_pay (F:Finset J): Round φ T (fun i=>(∏ x∈ F,g i x) / area D v (s i) F):=by
   have hx (x:J) : Round φ T (fun i=> g i x/s i (par D x.val)^v x):=by
       let y0 i:=s i (par D x.val); have hx:= parent_middle D h (x:=x.val) (mem_union_right _ x.2); have hb:= stands D hG A h b hx; obtain ⟨_,hs⟩:= arrive D hG A h b d (v:=x.val) (mem_union_right _ x.2)
       refine ((hw x).mul ((hs.div hb).power 4 h.ray)).adjust ?_; filter_upwards [(h.fade _ hx).eventually self_mem_nhdsWithin] with i hi; let j':= finishAt D (Y i) x.val; let y:=y0 i; have hp:0<y:=hi
       change w i x/y^_* (C.S.a _/y/(C.S.a j' / y))^4 = (w i x*(C.S.a _/C.S.a j')^4)/y^_; field_simp
   apply (Round.multiple F _ h.ray (fun i _=> hx i)).adjust; filter_upwards with i; rw [Finset.prod_div_distrib]; rfl
local notation "R!" => fun i=> (s i (par D u)/s i u)^d'
set_option quotPrecheck false
variable (hz:Round φ T z)(hc:Round φ T c)(hr:Round φ T (fun i=> r i / area D v (s i) (cove D U u)))
include hu hz hc hr
lemma purse_fund : Round φ T (fun i=> purse D C u (Y i) (p i) U d' (j i) W (r i) (z i) (c i) (g i)/(volume D U v (s i)*R! i)):=by
   have hV:=area_pay D A hG b d h v hw Π!; have hq : par D u∈U:= h.crowned.roots (par_le D u) hu; have hq':= (h.fade u hu).eventually self_mem_nhdsWithin; have hx':=(h.fade _ hq).eventually self_mem_nhdsWithin;
   let w' i:= K (p i u); let u' i:= K (j i); let v' i:=K (finishAt D (Y i) u); let f i:= Run.Below C.path ((lantern C.path (r i) d' (j i) (p i u))/2) (p i u) (finishAt D (Y i) u); let F i:=s i (par D u); let m i:=s i u; let t i:= (F i/m i)^d'; let a' i:= area D v (s i) Γ; let b' i:=area D v (s i) Π!
   have hp:Round φ T (fun i=>w' i/F i):=(arrive D hG A h b d (mem_union_left _ hu)).2; have hh:Round φ T (fun i=>u' i/m i):=(gleans D A hG b h hu).2.2; have hg:Round φ T (fun i=>v' i/F i):= stands D hG A h b hq
   have h₀:Round φ T (fun i=> f i/(a' i*t i)):=by
        refine ((((hr.div (Round.const zero_lt_two h.ray)).mul ((hp.div hh).power d' h.ray)).mul ((hp.div hg).power 4 h.ray))).adjust ?_
        filter_upwards [hq',hx',area_pos D h v Γ] with i hi hv he; have hq : 0 < m i:=hi; have hx:0 < F i:=hv; have ht:0<a' i:=he; have hμ:0<v' i:=C.S.a_pos _; have hφ:0<u' i:=C.S.a_pos _; unfold f Run.Below lantern; change r i/a' i /2*((w' i/F i)/(u' i/m i))^_ *(w' i/F i/(v' i/F i))^4 = r i*(w' i/ u' i)^d'/2*(w' i/v' i)^4/(a' i*(F i/m i)^d'); simp_rw [div_pow]; field_simp
   have h₁:Round φ T (fun i=> (event_fee W (c i))^(Fintype.card X)):=(hc.power _ h.ray).power _ h.ray
   apply ((((hz.power (U.card*(places X+places X)) h.ray).mul h₀).mul (h₁.mul h₁)).mul hV).adjust; filter_upwards with i; unfold purse; rw [area_volume D]; unfold f t a' F m; ring
end YM.OPE.Arboreal.Pixel

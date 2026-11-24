import YM.FormalBulk08.Hay.Pass

/-! Canonical cover transcription of kinetic book base. Pre-L widths here from width-R; A can specify path cost but loop budget does not choose repeated width. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Hay
open Filter Set Function MeasureTheory Lattice RG Exterior Wilson Precision Tree Work.F05
open Stationary hiding shine Rays
open Reef Series Wick Jets Orb Plait PowerSeries Lava Mesa Broc City Cork Lotus Shore Gorge Laurent
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{c f n:Side}{p:Clip}{R:PathData G}{j t m r e E:ℕ}{σ K B Z:ℝ}
lemma cold_add {f g:∀ n:Side,Link G n→ℝ}(hf:∀ n,AnalyticAt ℝ (f n) 0)(hg:∀ n,AnalyticAt ℝ (g n) 0){T S:Tile (edgeL G) (t+1)}(ht: Bail (fame _) σ T K)(hu:Bail (fame _) σ S B)(he:Matched T f)(hp:Matched S g)(hs:0≤σ): Matched (T+S) (fun n=> f n+g n):= by
   intro n; rw [cum_plus _ _ hs hs ht hu,he n,hp n];ext1 x; rw [Pi.add_apply, Broc.beam,Broc.beam,Broc.beam,Tensor.coeff,Tensor.coeff,Tensor.coeff,iteratedFDeriv_add_apply (hf n).contDiffAt (hg n).contDiffAt,smul_add];rfl
lemma booksK {T S: Pot G}(H:FloatK T)(V:FloatK S): ∀ n,stone (T+S) n= stone T n+ stone S n:= by
    intro n; ext1 i; rw [map_add];simp_rw [sow_coeff,sow];rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _;obtain ⟨η,A,x,p⟩:=H.fare i (j+1); obtain ⟨t,B,y,q⟩:=V.fare i (j+1); rw [←map_add];exact congr_arg _ (cum_plus 0 n x.le y.le p q)
-- translation for quadratic and signed orbit
lemma liaison (U:Config G n)(b:Site n): quadratic p R (pull 1 b U)=quadratic p R U:= by
   have he x: expandAt x (pull 1 b U)=expandAt (x+b) U:= by funext; rw [pull_one];simp [expandAt,Lattice.translate,add_assoc]
   have ht(x:Face (Per n)): faceValue (pull 1 b U) x= faceValue U (x.1+b,x.2):=by rw [faceValue,travel_pull]; simp only [affine,Signed.act_one]; unfold faceValue square; simp
   let k:Face (Per n) ≃ Face (Per n):= Equiv.prodCongr (Equiv.addRight b) (Equiv.refl PlaqAxes); unfold quadratic;refine Fintype.sum_equiv k _ _ fun x=>?_ ; rw [ht]; have hx:R.ell (pull 1 b U) x=R.ell U (k x):= by unfold PathData.ell PathData.ellTerms Slot.atSite; simp_rw [he];rfl
   rw [hx];rfl
lemma second_coast (U:Config G n)(s:Signed)(b:Site n): secondTerm p R (pull s b U)=secondTerm p R U:= by
   unfold secondTerm; simp only [pull_pull,affine, Signed.act_zero,zero_add]; unfold Patch.average;apply congr_arg (fun x:ℝ=> (Fintype.card Signed:ℝ)⁻¹*x)
   refine Eq.trans (Finset.sum_congr rfl (g:=fun i=> quadratic p R (pull (s*i) 0 U)) ?_) (Equiv.sum_comp (Equiv.mulLeft s) (fun i:Signed=> quadratic p R (pull i 0 U)))
   intro i _; let c:=s*i;have h:pull c b U=pull 1 (c⁻¹.act b) (pull c 0 U):= by rw [pull_pull]; simp [affine]
   change quadratic _ _ (pull c b U)=_;rw [h,liaison]
lemma main_coast (U:Config G n)(s: Signed)(b:Site n): mainTerm p R (pull s b U)= mainTerm p R U:= by
   have hh (U:Config G n): mainTerm p R U= secondTerm p R U + orbitRaw R.cubic U + orbitRaw R.quartic U:= by simp only [mainTerm, secondTerm, orbitRaw,Patch.average,Finset.sum_add_distrib,mul_add]
   rw [hh,hh,second_coast,raw_coast,raw_coast]
-- L kernel all-grade construction. Width Ω under cost stage.
variable (G)
lemma main_money (σ K Z:ℝ)(j:ℕ)(hs:0<σ)(hK:0≤K)(hZ:0≤Z) : ∃ η C:ℝ,0<η ∧ 0≤ C ∧ ∀ (p:Clip) (R:PathData G) B,p.direct≤ Z→R.Bounds p σ K B→ ∃ T:Tile (edgeL G) (j+1), Up T ∧ Bail (fame _) η T C ∧ Matched T (fun n=>intended p R (m:=n)) := by
    obtain ⟨s,C,ht,H,h⟩:= column_price G j K Z hs hZ
    obtain ⟨τ,c,hτ,hc,F⟩:=play_boom G 3 j hs; obtain ⟨θ,D,hθ,hD,L⟩:=play_boom G 4 j hs
    let w:=s/2/2; let A:=C*radioCost G s j; let x:=min (min τ θ) w; let B:=A+K*c+K*D
    have ha:0≤A:=mul_nonneg H (radio_charges G j ht); have hy:0<x:= by unfold x w; positivity
    refine ⟨x,B,hy,by unfold B; positivity,fun p R Λ Hk hx=>?_⟩
    obtain ⟨h₀,T,hT,H⟩:=h p R _ _ _ Hk hx hx.rows;let X:=radio T;have hh: Bail (fame _) x X A:= (radio_money hT ht (by assumption)).shrink (min_le_right ..)
    let m:= fun a:Side=> inputSeries p R (m:=a)
    have hm := radio_matched hT (f:=m) H ht (by assumption)
    obtain ⟨T3,HT,h3,u⟩:= F R.cubic K ⟨hx.three,fun i=> (hx.invariant i).2.1⟩
    obtain ⟨T4,H',h4,v⟩:= L R.quartic K ⟨hx.four,fun i=> (hx.invariant i).2.2⟩
    have hB:= HT.shrink (show x≤τ from (min_le_left ..).trans (min_le_left ..))
    have hg:= H'.shrink (show x≤θ from (min_le_left ..).trans (min_le_right ..))
    have hp a: AnalyticAt ℝ (turnSeries R.cubic (m:=a)) 0:= turns_analytic R.cubic hs hx.three
    have hw:= cold_add h₀ hp hh hB hm u hy.le
    refine ⟨X+T3+T4,((Up.add (radio_up _) h3).add h4),(hh.add hB).add hg,fun n=>?_⟩
    change _=Broc.beam (intended p R (m:=n)) _;rw [Stationary.intent]; exact cold_add (fun n=> (h₀ n).add (hp n)) (fun n=> turns_analytic R.quartic hs hx.four) (hh.add hB) hg hw v hy.le n
-- convert to negative classical representative
lemma kernel_civic (n:Side)(hp:R.Bounds p σ K B)(hs:G.Simple): Civic (-afterX (paste (intended p R (m:=n))) 2) := by
    intro s x I d a b u ha hb hA hB hu hx ht; have hz:intended p R (m:=n)∘ a=ᶠ[𝓝 0] intended p R ∘ b:= ht.mono fun j hk=> by simp only [Function.comp_apply,intended,hk, mainTerm_gauge hp,main_coast]
    let f:=intended p R (m:=n); have hv:= (strain p R hp (m:=n))
    have hQ:coeff 1 (paste f)=0:=by rw [paste_coeff,point_quiet hs hv 1 (by omega) Nat.one_pos]; simp [laden]
    rw [map_neg,map_neg,reads_lane _ hQ _ (paste_first f),reads_lane _ hQ _ (paste_first f),← paste_steps f a hv.analytic.contDiffAt (hA.of_le le_top) ha,← paste_steps f b hv.analytic.contDiffAt (hB.of_le le_top) hb, paste_replace hz]
end YM.FormalBulk08.Hay

import YM.XSpace.Harbor
/-!
# T diagnostic tangent null on these actual frames. No tensor-wick conventions shortcuts
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Tornado
open Function Set Filter Lattice Trace Chart2 Maxwell Maxwell.Free Maxwell.Wick Photo Cirrus Foundation Chiral Graph3 Stall Playpen Future Mu JetGauge Pages Next.Rank.Normal MvPolynomial Structure1 Normalize Relief AxesTangent
open scoped Topology BigOperators InnerProductSpace Classical
variable {G:Gauge}{n:ℕ}
abbrev Tbk(G:Gauge):= en (le_refl 6) (Bfield G)
abbrev Tuk(G:Gauge):= en (show 4≤6 by decide) (Ufield G)
lemma tk0 : token G= trip (Tbk G) (Tuk G) (Tuk G):=rfl
lemma bknots : hinge 6 (Tbk G)= -Tbk G:=Subtype.ext b_turn
lemma uknots : hinge 6 (Tuk G)= Tuk G:=Subtype.ext u_turn
lemma gust : SlotOdd (token G):=by
  intro F; rw [tk0]; let p:= trip (Tbk G) (Tuk G) (Tuk G); rw [show hinge 6 ∘ p = Function.update p 0 (-Tbk G) from funext fun i=> by fin_cases i <;> simp [p, bknots,uknots,trip]]; rw [MultilinearMap.map_update_neg,show Tbk G=p 0 from rfl, Function.update_eq_self]; rfl
variable (W:Initialize G)(g:G.Simple)
variable (p: Sec G 6)(q: Sec G 4)(w:Points 3)(h:w∈conf 3)
local notation "A" => Tbk G
local notation "B" => Tuk G
local notation "Y" => (token G)
abbrev years:= Gate w
abbrev loc (i:Fin n)(v:Sample n):= v.layout i
lemma landscape (i: Cirrus.Sample 3): i.layout= trip (loc 0 i) (loc 1 i) (loc 2 i):= funext fun j=> by fin_cases j <;> simp [loc,trip]
lemma expense (w:Points n)(X:Tags G 6 n)(h:w∈conf n): Tendsto (fun p=> blossom0 W 6 (unit p) p.layout X) (Gate w) (𝓝 (scene w 6 X)):=by
  have he := (notices W 6 X w h).sub (Bloom.spends w (landscape0 W 6 w X)); rw [sub_zero] at he; exact he.congr fun i=> sub_sub_cancel ..
lemma flight (w:Points n)(j k: Fin n): Relief.distance (Gate w) unit (fun i=> loc j i-loc k i) (w j-w k):=by
  have he:= fence (Gate w) (w j) (w k) (matched w j) (matched w k); apply he.congr; intro i; simp only [charts, sub_sub_sub_cancel_right] -- names?
lemma aurora (a:ℝ)(z x y:Cover): blossom0 W 6 a (trip z x y) (trip p B B)=
    base a^8 * F3 (Trace.volume z (openP W p a)) (u_w W x) (u_w W y):=by
  unfold blossom0; rw [LinearMap.compMultilinearMap_apply,winds,Fin.prod_univ_three]; simp only [peg₀,peg₁,peg₂,Tuk,begins W a] -- order μ0 F p argument implicit
  rw [open_loc W p,ζ_value]; rw [mul_assoc,smul_mul_smul,mul_smul_comm,map_smul,← pow_add]; rfl
include W g h in
lemma reaches : scene w 6 (trip p B B)=0:=by
  let x:= loc (n:=3) 1; let y:=loc (n:=3) 2; let z:=loc (n:=3) 0; let P(i):=openP W p (unit (n:=3) i); have S:Relief.Stage (Gate w) Cirrus.unit:= ⟨stepG w,Eventually.of_forall unit_pos⟩; have hh:Injective w.ofLp:=h; have he:= flight w 1 0; have hv:= flight w 2 0;
  have ht:= lowest W g S he hv (by rintro f; exact hh.ne (by decide : (1:Fin 3) ≠2) (sub_left_inj.mp f)) (P:=P) (pays_records W g S he hv (opening W p) (sub_ne_zero.mpr (hh.ne (by decide : (1:Fin 3)≠0))) (sub_ne_zero.mpr (hh.ne (by decide : (2:Fin 3)≠0))))
  refine tendsto_nhds_unique (expense W w (trip p B B) h) (ht.congr (fun i=>?_)); rw [show i.layout=_ from landscape i, aurora W p,color_mix W g, slaughter W g _ _ _ ?_, zero_add]; rfl; exact openPV W p _ _
-- U low possible changes: refer to parity, strong argument with rank not needed
variable (F:FieldEnd G 6) (hp:F∈ Tri G 6)
lemma sits_odd (P:Sec G 6)(h: hinge 6 P=P) (C: Sec G 6)(H: hinge 6 C=C) : SlotOdd (trip A P C):=by
  intro F; let p:=trip A P C; rw [show hinge 6 ∘ p = Function.update p 0 (-A) from funext fun i=> by fin_cases i <;> simp [p, bknots,h,H, trip]]; rw [MultilinearMap.map_update_neg,show A=p 0 from rfl, Function.update_eq_self]; rfl
lemma even_zero (w:Points n)(X:Tags G 6 n)(h:w∈conf n)(H:SlotOdd X): scene w 6 X=0:=by
  have hp : scene w 6 (hinge 6 ∘ X)=scene w 6 X:= Normalize.free_symmetry _ h; have h0:=(H (scene w 6)); rw [hp] at h0; linear_combination h0 / 2
lemma U_bottom : Tuk G= up (show 4≤6 by decide) (en (le_refl 4) (Ufield G)):=rfl
include W g h hp in
theorem ignored : lot (scene w 6) F Y=0:=by
  let V:= F B; have h0:hinge 6 V=V:=by
    have ht:= (tri_may F).1 hp; unfold Tuk at *; exact Subtype.ext (same_low g V.val (ht.2 _ (show 4≤6 by decide) _ (Ufield G).property.1))
  rw [lots,Fin.sum_univ_three]; rw [show Function.update Y 0 (F (Y 0))=trip (F A) B B from funext fun i=>by fin_cases i <;> simp [trip,token,Tuk,Tbk]]; -- compiler might convert
  rw [show Function.update Y 1 (F (Y 1))=trip A V B from funext fun i=>by fin_cases i <;> simp [trip,token,V,Tuk,Tbk], show Function.update Y 2 (F (Y 2))=trip A B V from funext fun i=>by fin_cases i <;> simp [trip,token, token,V,Tuk,Tbk]]
  rw [reaches W g _ w h, even_zero _ _ h (sits_odd V h0 B uknots), even_zero _ _ h (sits_odd B uknots V h0),zero_add,zero_add]
end YM.XSpace.Tornado

import JT58.CertificateData

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace JT58

def corePresent (s : Selection) : Bool :=
  coreEdgeLists.any (fun es => es.all s)

def coverAvailable (s : Selection) : Bool :=
  coverCertificates.any (fun d => d.Permitted s)

theorem core_witness_0 (s : Selection) (h0 : s 0 = true) (h1 : s 1 = true) (h2 : s 2 = true) (h4 : s 4 = true) (h5 : s 5 = true) (h14 : s 14 = true) :
    (corePresent s || coverAvailable s) = true := by
  have h : corePresent s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coreEdges 0, by decide, ?_⟩
    change ([0, 1, 2, 4, 5, 14] : List (Fin 19)).all s = true
    simp [h0, h1, h2, h4, h5, h14]
  simp [h]

theorem core_witness_1 (s : Selection) (h7 : s 7 = true) (h8 : s 8 = true) (h9 : s 9 = true) (h11 : s 11 = true) (h12 : s 12 = true) (h17 : s 17 = true) :
    (corePresent s || coverAvailable s) = true := by
  have h : corePresent s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coreEdges 1, by decide, ?_⟩
    change ([7, 8, 9, 11, 12, 17] : List (Fin 19)).all s = true
    simp [h7, h8, h9, h11, h12, h17]
  simp [h]

theorem core_witness_2 (s : Selection) (h7 : s 7 = true) (h9 : s 9 = true) (h10 : s 10 = true) (h12 : s 12 = true) (h13 : s 13 = true) (h18 : s 18 = true) :
    (corePresent s || coverAvailable s) = true := by
  have h : corePresent s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coreEdges 2, by decide, ?_⟩
    change ([7, 9, 10, 12, 13, 18] : List (Fin 19)).all s = true
    simp [h7, h9, h10, h12, h13, h18]
  simp [h]

theorem core_witness_3 (s : Selection) (h0 : s 0 = true) (h1 : s 1 = true) (h3 : s 3 = true) (h4 : s 4 = true) (h6 : s 6 = true) (h7 : s 7 = true) (h8 : s 8 = true) (h10 : s 10 = true) (h11 : s 11 = true) (h13 : s 13 = true) (h15 : s 15 = true) :
    (corePresent s || coverAvailable s) = true := by
  have h : corePresent s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coreEdges 3, by decide, ?_⟩
    change ([0, 1, 3, 4, 6, 7, 8, 10, 11, 13, 15] : List (Fin 19)).all s = true
    simp [h0, h1, h3, h4, h6, h7, h8, h10, h11, h13, h15]
  simp [h]

theorem core_witness_4 (s : Selection) (h0 : s 0 = true) (h1 : s 1 = true) (h3 : s 3 = true) (h4 : s 4 = true) (h6 : s 6 = true) (h8 : s 8 = true) (h9 : s 9 = true) (h10 : s 10 = true) (h15 : s 15 = true) (h17 : s 17 = true) (h18 : s 18 = true) :
    (corePresent s || coverAvailable s) = true := by
  have h : corePresent s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coreEdges 4, by decide, ?_⟩
    change ([0, 1, 3, 4, 6, 8, 9, 10, 15, 17, 18] : List (Fin 19)).all s = true
    simp [h0, h1, h3, h4, h6, h8, h9, h10, h15, h17, h18]
  simp [h]

theorem core_witness_5 (s : Selection) (h0 : s 0 = true) (h1 : s 1 = true) (h3 : s 3 = true) (h4 : s 4 = true) (h6 : s 6 = true) (h11 : s 11 = true) (h12 : s 12 = true) (h13 : s 13 = true) (h15 : s 15 = true) (h17 : s 17 = true) (h18 : s 18 = true) :
    (corePresent s || coverAvailable s) = true := by
  have h : corePresent s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coreEdges 5, by decide, ?_⟩
    change ([0, 1, 3, 4, 6, 11, 12, 13, 15, 17, 18] : List (Fin 19)).all s = true
    simp [h0, h1, h3, h4, h6, h11, h12, h13, h15, h17, h18]
  simp [h]

theorem core_witness_6 (s : Selection) (h0 : s 0 = true) (h2 : s 2 = true) (h3 : s 3 = true) (h5 : s 5 = true) (h6 : s 6 = true) (h7 : s 7 = true) (h8 : s 8 = true) (h10 : s 10 = true) (h11 : s 11 = true) (h13 : s 13 = true) (h16 : s 16 = true) :
    (corePresent s || coverAvailable s) = true := by
  have h : corePresent s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coreEdges 6, by decide, ?_⟩
    change ([0, 2, 3, 5, 6, 7, 8, 10, 11, 13, 16] : List (Fin 19)).all s = true
    simp [h0, h2, h3, h5, h6, h7, h8, h10, h11, h13, h16]
  simp [h]

theorem core_witness_7 (s : Selection) (h0 : s 0 = true) (h2 : s 2 = true) (h3 : s 3 = true) (h5 : s 5 = true) (h6 : s 6 = true) (h8 : s 8 = true) (h9 : s 9 = true) (h10 : s 10 = true) (h16 : s 16 = true) (h17 : s 17 = true) (h18 : s 18 = true) :
    (corePresent s || coverAvailable s) = true := by
  have h : corePresent s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coreEdges 7, by decide, ?_⟩
    change ([0, 2, 3, 5, 6, 8, 9, 10, 16, 17, 18] : List (Fin 19)).all s = true
    simp [h0, h2, h3, h5, h6, h8, h9, h10, h16, h17, h18]
  simp [h]

theorem core_witness_8 (s : Selection) (h0 : s 0 = true) (h2 : s 2 = true) (h3 : s 3 = true) (h5 : s 5 = true) (h6 : s 6 = true) (h11 : s 11 = true) (h12 : s 12 = true) (h13 : s 13 = true) (h16 : s 16 = true) (h17 : s 17 = true) (h18 : s 18 = true) :
    (corePresent s || coverAvailable s) = true := by
  have h : corePresent s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coreEdges 8, by decide, ?_⟩
    change ([0, 2, 3, 5, 6, 11, 12, 13, 16, 17, 18] : List (Fin 19)).all s = true
    simp [h0, h2, h3, h5, h6, h11, h12, h13, h16, h17, h18]
  simp [h]

theorem core_witness_9 (s : Selection) (h1 : s 1 = true) (h2 : s 2 = true) (h3 : s 3 = true) (h7 : s 7 = true) (h8 : s 8 = true) (h10 : s 10 = true) (h11 : s 11 = true) (h13 : s 13 = true) (h14 : s 14 = true) (h15 : s 15 = true) (h16 : s 16 = true) :
    (corePresent s || coverAvailable s) = true := by
  have h : corePresent s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coreEdges 9, by decide, ?_⟩
    change ([1, 2, 3, 7, 8, 10, 11, 13, 14, 15, 16] : List (Fin 19)).all s = true
    simp [h1, h2, h3, h7, h8, h10, h11, h13, h14, h15, h16]
  simp [h]

theorem core_witness_10 (s : Selection) (h1 : s 1 = true) (h2 : s 2 = true) (h3 : s 3 = true) (h8 : s 8 = true) (h9 : s 9 = true) (h10 : s 10 = true) (h14 : s 14 = true) (h15 : s 15 = true) (h16 : s 16 = true) (h17 : s 17 = true) (h18 : s 18 = true) :
    (corePresent s || coverAvailable s) = true := by
  have h : corePresent s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coreEdges 10, by decide, ?_⟩
    change ([1, 2, 3, 8, 9, 10, 14, 15, 16, 17, 18] : List (Fin 19)).all s = true
    simp [h1, h2, h3, h8, h9, h10, h14, h15, h16, h17, h18]
  simp [h]

theorem core_witness_11 (s : Selection) (h1 : s 1 = true) (h2 : s 2 = true) (h3 : s 3 = true) (h11 : s 11 = true) (h12 : s 12 = true) (h13 : s 13 = true) (h14 : s 14 = true) (h15 : s 15 = true) (h16 : s 16 = true) (h17 : s 17 = true) (h18 : s 18 = true) :
    (corePresent s || coverAvailable s) = true := by
  have h : corePresent s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coreEdges 11, by decide, ?_⟩
    change ([1, 2, 3, 11, 12, 13, 14, 15, 16, 17, 18] : List (Fin 19)).all s = true
    simp [h1, h2, h3, h11, h12, h13, h14, h15, h16, h17, h18]
  simp [h]

theorem core_witness_12 (s : Selection) (h4 : s 4 = true) (h5 : s 5 = true) (h6 : s 6 = true) (h7 : s 7 = true) (h8 : s 8 = true) (h10 : s 10 = true) (h11 : s 11 = true) (h13 : s 13 = true) (h14 : s 14 = true) (h15 : s 15 = true) (h16 : s 16 = true) :
    (corePresent s || coverAvailable s) = true := by
  have h : corePresent s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coreEdges 12, by decide, ?_⟩
    change ([4, 5, 6, 7, 8, 10, 11, 13, 14, 15, 16] : List (Fin 19)).all s = true
    simp [h4, h5, h6, h7, h8, h10, h11, h13, h14, h15, h16]
  simp [h]

theorem core_witness_13 (s : Selection) (h4 : s 4 = true) (h5 : s 5 = true) (h6 : s 6 = true) (h8 : s 8 = true) (h9 : s 9 = true) (h10 : s 10 = true) (h14 : s 14 = true) (h15 : s 15 = true) (h16 : s 16 = true) (h17 : s 17 = true) (h18 : s 18 = true) :
    (corePresent s || coverAvailable s) = true := by
  have h : corePresent s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coreEdges 13, by decide, ?_⟩
    change ([4, 5, 6, 8, 9, 10, 14, 15, 16, 17, 18] : List (Fin 19)).all s = true
    simp [h4, h5, h6, h8, h9, h10, h14, h15, h16, h17, h18]
  simp [h]

theorem core_witness_14 (s : Selection) (h4 : s 4 = true) (h5 : s 5 = true) (h6 : s 6 = true) (h11 : s 11 = true) (h12 : s 12 = true) (h13 : s 13 = true) (h14 : s 14 = true) (h15 : s 15 = true) (h16 : s 16 = true) (h17 : s 17 = true) (h18 : s 18 = true) :
    (corePresent s || coverAvailable s) = true := by
  have h : corePresent s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coreEdges 14, by decide, ?_⟩
    change ([4, 5, 6, 11, 12, 13, 14, 15, 16, 17, 18] : List (Fin 19)).all s = true
    simp [h4, h5, h6, h11, h12, h13, h14, h15, h16, h17, h18]
  simp [h]

theorem color_witness_0 (s : Selection) (h14 : s 14 = false) (h15 : s 15 = false) (h16 : s 16 = false) (h17 : s 17 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[0]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h14, h15, h16, h17, h18]
  simp [h]

theorem color_witness_1 (s : Selection) (h5 : s 5 = false) (h6 : s 6 = false) (h16 : s 16 = false) (h17 : s 17 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[1]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h5, h6, h16, h17, h18]
  simp [h]

theorem color_witness_2 (s : Selection) (h4 : s 4 = false) (h16 : s 16 = false) (h17 : s 17 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[2]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h4, h16, h17, h18]
  simp [h]

theorem color_witness_3 (s : Selection) (h2 : s 2 = false) (h3 : s 3 = false) (h16 : s 16 = false) (h17 : s 17 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[3]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h2, h3, h16, h17, h18]
  simp [h]

theorem color_witness_4 (s : Selection) (h1 : s 1 = false) (h16 : s 16 = false) (h17 : s 17 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[4]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h16, h17, h18]
  simp [h]

theorem color_witness_5 (s : Selection) (h0 : s 0 = false) (h16 : s 16 = false) (h17 : s 17 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[5]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h16, h17, h18]
  simp [h]

theorem color_witness_6 (s : Selection) (h4 : s 4 = false) (h6 : s 6 = false) (h15 : s 15 = false) (h17 : s 17 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[6]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h4, h6, h15, h17, h18]
  simp [h]

theorem color_witness_7 (s : Selection) (h5 : s 5 = false) (h15 : s 15 = false) (h17 : s 17 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[7]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h5, h15, h17, h18]
  simp [h]

theorem color_witness_8 (s : Selection) (h1 : s 1 = false) (h3 : s 3 = false) (h15 : s 15 = false) (h17 : s 17 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[8]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h3, h15, h17, h18]
  simp [h]

theorem color_witness_9 (s : Selection) (h2 : s 2 = false) (h15 : s 15 = false) (h17 : s 17 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[9]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h2, h15, h17, h18]
  simp [h]

theorem color_witness_10 (s : Selection) (h0 : s 0 = false) (h15 : s 15 = false) (h17 : s 17 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[10]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h15, h17, h18]
  simp [h]

theorem color_witness_11 (s : Selection) (h6 : s 6 = false) (h14 : s 14 = false) (h17 : s 17 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[11]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h6, h14, h17, h18]
  simp [h]

theorem color_witness_12 (s : Selection) (h4 : s 4 = false) (h5 : s 5 = false) (h14 : s 14 = false) (h17 : s 17 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[12]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h4, h5, h14, h17, h18]
  simp [h]

theorem color_witness_13 (s : Selection) (h3 : s 3 = false) (h14 : s 14 = false) (h17 : s 17 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[13]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h3, h14, h17, h18]
  simp [h]

theorem color_witness_14 (s : Selection) (h1 : s 1 = false) (h2 : s 2 = false) (h14 : s 14 = false) (h17 : s 17 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[14]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h2, h14, h17, h18]
  simp [h]

theorem color_witness_15 (s : Selection) (h0 : s 0 = false) (h14 : s 14 = false) (h17 : s 17 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[15]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h14, h17, h18]
  simp [h]

theorem color_witness_16 (s : Selection) (h0 : s 0 = false) (h3 : s 3 = false) (h6 : s 6 = false) (h17 : s 17 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[16]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h3, h6, h17, h18]
  simp [h]

theorem color_witness_17 (s : Selection) (h2 : s 2 = false) (h6 : s 6 = false) (h17 : s 17 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[17]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h2, h6, h17, h18]
  simp [h]

theorem color_witness_18 (s : Selection) (h1 : s 1 = false) (h6 : s 6 = false) (h17 : s 17 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[18]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h6, h17, h18]
  simp [h]

theorem color_witness_19 (s : Selection) (h3 : s 3 = false) (h5 : s 5 = false) (h17 : s 17 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[19]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h3, h5, h17, h18]
  simp [h]

theorem color_witness_20 (s : Selection) (h0 : s 0 = false) (h2 : s 2 = false) (h5 : s 5 = false) (h17 : s 17 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[20]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h2, h5, h17, h18]
  simp [h]

theorem color_witness_21 (s : Selection) (h1 : s 1 = false) (h5 : s 5 = false) (h17 : s 17 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[21]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h5, h17, h18]
  simp [h]

theorem color_witness_22 (s : Selection) (h3 : s 3 = false) (h4 : s 4 = false) (h17 : s 17 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[22]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h3, h4, h17, h18]
  simp [h]

theorem color_witness_23 (s : Selection) (h2 : s 2 = false) (h4 : s 4 = false) (h17 : s 17 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[23]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h2, h4, h17, h18]
  simp [h]

theorem color_witness_24 (s : Selection) (h0 : s 0 = false) (h1 : s 1 = false) (h4 : s 4 = false) (h17 : s 17 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[24]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h1, h4, h17, h18]
  simp [h]

theorem color_witness_25 (s : Selection) (h12 : s 12 = false) (h13 : s 13 = false) (h14 : s 14 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[25]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h12, h13, h14, h18]
  simp [h]

theorem color_witness_26 (s : Selection) (h11 : s 11 = false) (h14 : s 14 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[26]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h11, h14, h18]
  simp [h]

theorem color_witness_27 (s : Selection) (h9 : s 9 = false) (h10 : s 10 = false) (h14 : s 14 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[27]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h9, h10, h14, h18]
  simp [h]

theorem color_witness_28 (s : Selection) (h8 : s 8 = false) (h14 : s 14 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[28]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h8, h14, h18]
  simp [h]

theorem color_witness_29 (s : Selection) (h7 : s 7 = false) (h14 : s 14 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[29]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h7, h14, h18]
  simp [h]

theorem color_witness_30 (s : Selection) (h5 : s 5 = false) (h12 : s 12 = false) (h13 : s 13 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[30]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h5, h12, h13, h18]
  simp [h]

theorem color_witness_31 (s : Selection) (h4 : s 4 = false) (h12 : s 12 = false) (h13 : s 13 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[31]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h4, h12, h13, h18]
  simp [h]

theorem color_witness_32 (s : Selection) (h2 : s 2 = false) (h12 : s 12 = false) (h13 : s 13 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[32]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h2, h12, h13, h18]
  simp [h]

theorem color_witness_33 (s : Selection) (h1 : s 1 = false) (h12 : s 12 = false) (h13 : s 13 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[33]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h12, h13, h18]
  simp [h]

theorem color_witness_34 (s : Selection) (h0 : s 0 = false) (h12 : s 12 = false) (h13 : s 13 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[34]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h12, h13, h18]
  simp [h]

theorem color_witness_35 (s : Selection) (h5 : s 5 = false) (h11 : s 11 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[35]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h5, h11, h18]
  simp [h]

theorem color_witness_36 (s : Selection) (h4 : s 4 = false) (h11 : s 11 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[36]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h4, h11, h18]
  simp [h]

theorem color_witness_37 (s : Selection) (h2 : s 2 = false) (h11 : s 11 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[37]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h2, h11, h18]
  simp [h]

theorem color_witness_38 (s : Selection) (h1 : s 1 = false) (h11 : s 11 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[38]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h11, h18]
  simp [h]

theorem color_witness_39 (s : Selection) (h0 : s 0 = false) (h11 : s 11 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[39]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h11, h18]
  simp [h]

theorem color_witness_40 (s : Selection) (h5 : s 5 = false) (h9 : s 9 = false) (h10 : s 10 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[40]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h5, h9, h10, h18]
  simp [h]

theorem color_witness_41 (s : Selection) (h4 : s 4 = false) (h9 : s 9 = false) (h10 : s 10 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[41]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h4, h9, h10, h18]
  simp [h]

theorem color_witness_42 (s : Selection) (h2 : s 2 = false) (h9 : s 9 = false) (h10 : s 10 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[42]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h2, h9, h10, h18]
  simp [h]

theorem color_witness_43 (s : Selection) (h1 : s 1 = false) (h9 : s 9 = false) (h10 : s 10 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[43]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h9, h10, h18]
  simp [h]

theorem color_witness_44 (s : Selection) (h0 : s 0 = false) (h9 : s 9 = false) (h10 : s 10 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[44]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h9, h10, h18]
  simp [h]

theorem color_witness_45 (s : Selection) (h5 : s 5 = false) (h8 : s 8 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[45]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h5, h8, h18]
  simp [h]

theorem color_witness_46 (s : Selection) (h4 : s 4 = false) (h8 : s 8 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[46]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h4, h8, h18]
  simp [h]

theorem color_witness_47 (s : Selection) (h2 : s 2 = false) (h8 : s 8 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[47]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h2, h8, h18]
  simp [h]

theorem color_witness_48 (s : Selection) (h1 : s 1 = false) (h8 : s 8 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[48]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h8, h18]
  simp [h]

theorem color_witness_49 (s : Selection) (h0 : s 0 = false) (h8 : s 8 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[49]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h8, h18]
  simp [h]

theorem color_witness_50 (s : Selection) (h5 : s 5 = false) (h7 : s 7 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[50]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h5, h7, h18]
  simp [h]

theorem color_witness_51 (s : Selection) (h4 : s 4 = false) (h7 : s 7 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[51]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h4, h7, h18]
  simp [h]

theorem color_witness_52 (s : Selection) (h2 : s 2 = false) (h7 : s 7 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[52]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h2, h7, h18]
  simp [h]

theorem color_witness_53 (s : Selection) (h1 : s 1 = false) (h7 : s 7 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[53]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h7, h18]
  simp [h]

theorem color_witness_54 (s : Selection) (h0 : s 0 = false) (h7 : s 7 = false) (h18 : s 18 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[54]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h7, h18]
  simp [h]

theorem color_witness_55 (s : Selection) (h13 : s 13 = false) (h14 : s 14 = false) (h17 : s 17 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[55]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h13, h14, h17]
  simp [h]

theorem color_witness_56 (s : Selection) (h11 : s 11 = false) (h12 : s 12 = false) (h14 : s 14 = false) (h17 : s 17 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[56]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h11, h12, h14, h17]
  simp [h]

theorem color_witness_57 (s : Selection) (h10 : s 10 = false) (h14 : s 14 = false) (h17 : s 17 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[57]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h10, h14, h17]
  simp [h]

theorem color_witness_58 (s : Selection) (h8 : s 8 = false) (h9 : s 9 = false) (h14 : s 14 = false) (h17 : s 17 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[58]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h8, h9, h14, h17]
  simp [h]

theorem color_witness_59 (s : Selection) (h7 : s 7 = false) (h14 : s 14 = false) (h17 : s 17 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[59]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h7, h14, h17]
  simp [h]

theorem color_witness_60 (s : Selection) (h5 : s 5 = false) (h13 : s 13 = false) (h17 : s 17 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[60]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h5, h13, h17]
  simp [h]

theorem color_witness_61 (s : Selection) (h4 : s 4 = false) (h13 : s 13 = false) (h17 : s 17 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[61]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h4, h13, h17]
  simp [h]

theorem color_witness_62 (s : Selection) (h2 : s 2 = false) (h13 : s 13 = false) (h17 : s 17 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[62]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h2, h13, h17]
  simp [h]

theorem color_witness_63 (s : Selection) (h1 : s 1 = false) (h13 : s 13 = false) (h17 : s 17 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[63]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h13, h17]
  simp [h]

theorem color_witness_64 (s : Selection) (h0 : s 0 = false) (h13 : s 13 = false) (h17 : s 17 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[64]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h13, h17]
  simp [h]

theorem color_witness_65 (s : Selection) (h5 : s 5 = false) (h11 : s 11 = false) (h12 : s 12 = false) (h17 : s 17 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[65]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h5, h11, h12, h17]
  simp [h]

theorem color_witness_66 (s : Selection) (h4 : s 4 = false) (h11 : s 11 = false) (h12 : s 12 = false) (h17 : s 17 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[66]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h4, h11, h12, h17]
  simp [h]

theorem color_witness_67 (s : Selection) (h2 : s 2 = false) (h11 : s 11 = false) (h12 : s 12 = false) (h17 : s 17 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[67]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h2, h11, h12, h17]
  simp [h]

theorem color_witness_68 (s : Selection) (h1 : s 1 = false) (h11 : s 11 = false) (h12 : s 12 = false) (h17 : s 17 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[68]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h11, h12, h17]
  simp [h]

theorem color_witness_69 (s : Selection) (h0 : s 0 = false) (h11 : s 11 = false) (h12 : s 12 = false) (h17 : s 17 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[69]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h11, h12, h17]
  simp [h]

theorem color_witness_70 (s : Selection) (h5 : s 5 = false) (h10 : s 10 = false) (h17 : s 17 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[70]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h5, h10, h17]
  simp [h]

theorem color_witness_71 (s : Selection) (h4 : s 4 = false) (h10 : s 10 = false) (h17 : s 17 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[71]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h4, h10, h17]
  simp [h]

theorem color_witness_72 (s : Selection) (h2 : s 2 = false) (h10 : s 10 = false) (h17 : s 17 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[72]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h2, h10, h17]
  simp [h]

theorem color_witness_73 (s : Selection) (h1 : s 1 = false) (h10 : s 10 = false) (h17 : s 17 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[73]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h10, h17]
  simp [h]

theorem color_witness_74 (s : Selection) (h0 : s 0 = false) (h10 : s 10 = false) (h17 : s 17 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[74]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h10, h17]
  simp [h]

theorem color_witness_75 (s : Selection) (h5 : s 5 = false) (h8 : s 8 = false) (h9 : s 9 = false) (h17 : s 17 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[75]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h5, h8, h9, h17]
  simp [h]

theorem color_witness_76 (s : Selection) (h4 : s 4 = false) (h8 : s 8 = false) (h9 : s 9 = false) (h17 : s 17 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[76]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h4, h8, h9, h17]
  simp [h]

theorem color_witness_77 (s : Selection) (h2 : s 2 = false) (h8 : s 8 = false) (h9 : s 9 = false) (h17 : s 17 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[77]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h2, h8, h9, h17]
  simp [h]

theorem color_witness_78 (s : Selection) (h1 : s 1 = false) (h8 : s 8 = false) (h9 : s 9 = false) (h17 : s 17 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[78]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h8, h9, h17]
  simp [h]

theorem color_witness_79 (s : Selection) (h0 : s 0 = false) (h8 : s 8 = false) (h9 : s 9 = false) (h17 : s 17 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[79]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h8, h9, h17]
  simp [h]

theorem color_witness_80 (s : Selection) (h5 : s 5 = false) (h7 : s 7 = false) (h17 : s 17 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[80]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h5, h7, h17]
  simp [h]

theorem color_witness_81 (s : Selection) (h4 : s 4 = false) (h7 : s 7 = false) (h17 : s 17 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[81]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h4, h7, h17]
  simp [h]

theorem color_witness_82 (s : Selection) (h2 : s 2 = false) (h7 : s 7 = false) (h17 : s 17 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[82]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h2, h7, h17]
  simp [h]

theorem color_witness_83 (s : Selection) (h1 : s 1 = false) (h7 : s 7 = false) (h17 : s 17 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[83]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h7, h17]
  simp [h]

theorem color_witness_84 (s : Selection) (h0 : s 0 = false) (h7 : s 7 = false) (h17 : s 17 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[84]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h7, h17]
  simp [h]

theorem color_witness_85 (s : Selection) (h11 : s 11 = false) (h13 : s 13 = false) (h14 : s 14 = false) (h15 : s 15 = false) (h16 : s 16 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[85]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h11, h13, h14, h15, h16]
  simp [h]

theorem color_witness_86 (s : Selection) (h12 : s 12 = false) (h14 : s 14 = false) (h15 : s 15 = false) (h16 : s 16 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[86]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h12, h14, h15, h16]
  simp [h]

theorem color_witness_87 (s : Selection) (h8 : s 8 = false) (h10 : s 10 = false) (h14 : s 14 = false) (h15 : s 15 = false) (h16 : s 16 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[87]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h8, h10, h14, h15, h16]
  simp [h]

theorem color_witness_88 (s : Selection) (h9 : s 9 = false) (h14 : s 14 = false) (h15 : s 15 = false) (h16 : s 16 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[88]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h9, h14, h15, h16]
  simp [h]

theorem color_witness_89 (s : Selection) (h7 : s 7 = false) (h14 : s 14 = false) (h15 : s 15 = false) (h16 : s 16 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[89]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h7, h14, h15, h16]
  simp [h]

theorem color_witness_90 (s : Selection) (h5 : s 5 = false) (h6 : s 6 = false) (h11 : s 11 = false) (h13 : s 13 = false) (h16 : s 16 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[90]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h5, h6, h11, h13, h16]
  simp [h]

theorem color_witness_91 (s : Selection) (h4 : s 4 = false) (h11 : s 11 = false) (h13 : s 13 = false) (h16 : s 16 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[91]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h4, h11, h13, h16]
  simp [h]

theorem color_witness_92 (s : Selection) (h2 : s 2 = false) (h3 : s 3 = false) (h11 : s 11 = false) (h13 : s 13 = false) (h16 : s 16 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[92]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h2, h3, h11, h13, h16]
  simp [h]

theorem color_witness_93 (s : Selection) (h1 : s 1 = false) (h11 : s 11 = false) (h13 : s 13 = false) (h16 : s 16 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[93]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h11, h13, h16]
  simp [h]

theorem color_witness_94 (s : Selection) (h0 : s 0 = false) (h11 : s 11 = false) (h13 : s 13 = false) (h16 : s 16 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[94]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h11, h13, h16]
  simp [h]

theorem color_witness_95 (s : Selection) (h5 : s 5 = false) (h6 : s 6 = false) (h12 : s 12 = false) (h16 : s 16 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[95]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h5, h6, h12, h16]
  simp [h]

theorem color_witness_96 (s : Selection) (h4 : s 4 = false) (h12 : s 12 = false) (h16 : s 16 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[96]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h4, h12, h16]
  simp [h]

theorem color_witness_97 (s : Selection) (h2 : s 2 = false) (h3 : s 3 = false) (h12 : s 12 = false) (h16 : s 16 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[97]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h2, h3, h12, h16]
  simp [h]

theorem color_witness_98 (s : Selection) (h1 : s 1 = false) (h12 : s 12 = false) (h16 : s 16 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[98]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h12, h16]
  simp [h]

theorem color_witness_99 (s : Selection) (h0 : s 0 = false) (h12 : s 12 = false) (h16 : s 16 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[99]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h12, h16]
  simp [h]

theorem color_witness_100 (s : Selection) (h5 : s 5 = false) (h6 : s 6 = false) (h8 : s 8 = false) (h10 : s 10 = false) (h16 : s 16 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[100]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h5, h6, h8, h10, h16]
  simp [h]

theorem color_witness_101 (s : Selection) (h4 : s 4 = false) (h8 : s 8 = false) (h10 : s 10 = false) (h16 : s 16 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[101]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h4, h8, h10, h16]
  simp [h]

theorem color_witness_102 (s : Selection) (h2 : s 2 = false) (h3 : s 3 = false) (h8 : s 8 = false) (h10 : s 10 = false) (h16 : s 16 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[102]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h2, h3, h8, h10, h16]
  simp [h]

theorem color_witness_103 (s : Selection) (h1 : s 1 = false) (h8 : s 8 = false) (h10 : s 10 = false) (h16 : s 16 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[103]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h8, h10, h16]
  simp [h]

theorem color_witness_104 (s : Selection) (h0 : s 0 = false) (h8 : s 8 = false) (h10 : s 10 = false) (h16 : s 16 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[104]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h8, h10, h16]
  simp [h]

theorem color_witness_105 (s : Selection) (h5 : s 5 = false) (h6 : s 6 = false) (h9 : s 9 = false) (h16 : s 16 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[105]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h5, h6, h9, h16]
  simp [h]

theorem color_witness_106 (s : Selection) (h4 : s 4 = false) (h9 : s 9 = false) (h16 : s 16 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[106]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h4, h9, h16]
  simp [h]

theorem color_witness_107 (s : Selection) (h2 : s 2 = false) (h3 : s 3 = false) (h9 : s 9 = false) (h16 : s 16 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[107]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h2, h3, h9, h16]
  simp [h]

theorem color_witness_108 (s : Selection) (h1 : s 1 = false) (h9 : s 9 = false) (h16 : s 16 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[108]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h9, h16]
  simp [h]

theorem color_witness_109 (s : Selection) (h0 : s 0 = false) (h9 : s 9 = false) (h16 : s 16 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[109]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h9, h16]
  simp [h]

theorem color_witness_110 (s : Selection) (h5 : s 5 = false) (h6 : s 6 = false) (h7 : s 7 = false) (h16 : s 16 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[110]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h5, h6, h7, h16]
  simp [h]

theorem color_witness_111 (s : Selection) (h4 : s 4 = false) (h7 : s 7 = false) (h16 : s 16 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[111]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h4, h7, h16]
  simp [h]

theorem color_witness_112 (s : Selection) (h2 : s 2 = false) (h3 : s 3 = false) (h7 : s 7 = false) (h16 : s 16 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[112]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h2, h3, h7, h16]
  simp [h]

theorem color_witness_113 (s : Selection) (h1 : s 1 = false) (h7 : s 7 = false) (h16 : s 16 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[113]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h7, h16]
  simp [h]

theorem color_witness_114 (s : Selection) (h0 : s 0 = false) (h7 : s 7 = false) (h16 : s 16 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[114]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h7, h16]
  simp [h]

theorem color_witness_115 (s : Selection) (h4 : s 4 = false) (h6 : s 6 = false) (h11 : s 11 = false) (h13 : s 13 = false) (h15 : s 15 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[115]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h4, h6, h11, h13, h15]
  simp [h]

theorem color_witness_116 (s : Selection) (h5 : s 5 = false) (h11 : s 11 = false) (h13 : s 13 = false) (h15 : s 15 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[116]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h5, h11, h13, h15]
  simp [h]

theorem color_witness_117 (s : Selection) (h1 : s 1 = false) (h3 : s 3 = false) (h11 : s 11 = false) (h13 : s 13 = false) (h15 : s 15 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[117]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h3, h11, h13, h15]
  simp [h]

theorem color_witness_118 (s : Selection) (h2 : s 2 = false) (h11 : s 11 = false) (h13 : s 13 = false) (h15 : s 15 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[118]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h2, h11, h13, h15]
  simp [h]

theorem color_witness_119 (s : Selection) (h0 : s 0 = false) (h11 : s 11 = false) (h13 : s 13 = false) (h15 : s 15 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[119]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h11, h13, h15]
  simp [h]

theorem color_witness_120 (s : Selection) (h4 : s 4 = false) (h6 : s 6 = false) (h12 : s 12 = false) (h15 : s 15 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[120]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h4, h6, h12, h15]
  simp [h]

theorem color_witness_121 (s : Selection) (h5 : s 5 = false) (h12 : s 12 = false) (h15 : s 15 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[121]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h5, h12, h15]
  simp [h]

theorem color_witness_122 (s : Selection) (h1 : s 1 = false) (h3 : s 3 = false) (h12 : s 12 = false) (h15 : s 15 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[122]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h3, h12, h15]
  simp [h]

theorem color_witness_123 (s : Selection) (h2 : s 2 = false) (h12 : s 12 = false) (h15 : s 15 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[123]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h2, h12, h15]
  simp [h]

theorem color_witness_124 (s : Selection) (h0 : s 0 = false) (h12 : s 12 = false) (h15 : s 15 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[124]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h12, h15]
  simp [h]

theorem color_witness_125 (s : Selection) (h4 : s 4 = false) (h6 : s 6 = false) (h8 : s 8 = false) (h10 : s 10 = false) (h15 : s 15 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[125]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h4, h6, h8, h10, h15]
  simp [h]

theorem color_witness_126 (s : Selection) (h5 : s 5 = false) (h8 : s 8 = false) (h10 : s 10 = false) (h15 : s 15 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[126]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h5, h8, h10, h15]
  simp [h]

theorem color_witness_127 (s : Selection) (h1 : s 1 = false) (h3 : s 3 = false) (h8 : s 8 = false) (h10 : s 10 = false) (h15 : s 15 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[127]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h3, h8, h10, h15]
  simp [h]

theorem color_witness_128 (s : Selection) (h2 : s 2 = false) (h8 : s 8 = false) (h10 : s 10 = false) (h15 : s 15 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[128]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h2, h8, h10, h15]
  simp [h]

theorem color_witness_129 (s : Selection) (h0 : s 0 = false) (h8 : s 8 = false) (h10 : s 10 = false) (h15 : s 15 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[129]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h8, h10, h15]
  simp [h]

theorem color_witness_130 (s : Selection) (h4 : s 4 = false) (h6 : s 6 = false) (h9 : s 9 = false) (h15 : s 15 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[130]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h4, h6, h9, h15]
  simp [h]

theorem color_witness_131 (s : Selection) (h5 : s 5 = false) (h9 : s 9 = false) (h15 : s 15 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[131]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h5, h9, h15]
  simp [h]

theorem color_witness_132 (s : Selection) (h1 : s 1 = false) (h3 : s 3 = false) (h9 : s 9 = false) (h15 : s 15 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[132]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h3, h9, h15]
  simp [h]

theorem color_witness_133 (s : Selection) (h2 : s 2 = false) (h9 : s 9 = false) (h15 : s 15 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[133]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h2, h9, h15]
  simp [h]

theorem color_witness_134 (s : Selection) (h0 : s 0 = false) (h9 : s 9 = false) (h15 : s 15 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[134]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h9, h15]
  simp [h]

theorem color_witness_135 (s : Selection) (h4 : s 4 = false) (h6 : s 6 = false) (h7 : s 7 = false) (h15 : s 15 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[135]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h4, h6, h7, h15]
  simp [h]

theorem color_witness_136 (s : Selection) (h5 : s 5 = false) (h7 : s 7 = false) (h15 : s 15 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[136]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h5, h7, h15]
  simp [h]

theorem color_witness_137 (s : Selection) (h1 : s 1 = false) (h3 : s 3 = false) (h7 : s 7 = false) (h15 : s 15 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[137]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h3, h7, h15]
  simp [h]

theorem color_witness_138 (s : Selection) (h2 : s 2 = false) (h7 : s 7 = false) (h15 : s 15 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[138]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h2, h7, h15]
  simp [h]

theorem color_witness_139 (s : Selection) (h0 : s 0 = false) (h7 : s 7 = false) (h15 : s 15 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[139]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h7, h15]
  simp [h]

theorem color_witness_140 (s : Selection) (h6 : s 6 = false) (h11 : s 11 = false) (h13 : s 13 = false) (h14 : s 14 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[140]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h6, h11, h13, h14]
  simp [h]

theorem color_witness_141 (s : Selection) (h4 : s 4 = false) (h5 : s 5 = false) (h11 : s 11 = false) (h13 : s 13 = false) (h14 : s 14 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[141]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h4, h5, h11, h13, h14]
  simp [h]

theorem color_witness_142 (s : Selection) (h3 : s 3 = false) (h11 : s 11 = false) (h13 : s 13 = false) (h14 : s 14 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[142]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h3, h11, h13, h14]
  simp [h]

theorem color_witness_143 (s : Selection) (h1 : s 1 = false) (h2 : s 2 = false) (h11 : s 11 = false) (h13 : s 13 = false) (h14 : s 14 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[143]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h2, h11, h13, h14]
  simp [h]

theorem color_witness_144 (s : Selection) (h0 : s 0 = false) (h11 : s 11 = false) (h13 : s 13 = false) (h14 : s 14 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[144]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h11, h13, h14]
  simp [h]

theorem color_witness_145 (s : Selection) (h7 : s 7 = false) (h10 : s 10 = false) (h13 : s 13 = false) (h14 : s 14 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[145]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h7, h10, h13, h14]
  simp [h]

theorem color_witness_146 (s : Selection) (h9 : s 9 = false) (h13 : s 13 = false) (h14 : s 14 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[146]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h9, h13, h14]
  simp [h]

theorem color_witness_147 (s : Selection) (h8 : s 8 = false) (h13 : s 13 = false) (h14 : s 14 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[147]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h8, h13, h14]
  simp [h]

theorem color_witness_148 (s : Selection) (h10 : s 10 = false) (h12 : s 12 = false) (h14 : s 14 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[148]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h10, h12, h14]
  simp [h]

theorem color_witness_149 (s : Selection) (h7 : s 7 = false) (h9 : s 9 = false) (h12 : s 12 = false) (h14 : s 14 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[149]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h7, h9, h12, h14]
  simp [h]

theorem color_witness_150 (s : Selection) (h8 : s 8 = false) (h12 : s 12 = false) (h14 : s 14 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[150]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h8, h12, h14]
  simp [h]

theorem color_witness_151 (s : Selection) (h6 : s 6 = false) (h12 : s 12 = false) (h14 : s 14 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[151]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h6, h12, h14]
  simp [h]

theorem color_witness_152 (s : Selection) (h4 : s 4 = false) (h5 : s 5 = false) (h12 : s 12 = false) (h14 : s 14 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[152]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h4, h5, h12, h14]
  simp [h]

theorem color_witness_153 (s : Selection) (h3 : s 3 = false) (h12 : s 12 = false) (h14 : s 14 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[153]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h3, h12, h14]
  simp [h]

theorem color_witness_154 (s : Selection) (h1 : s 1 = false) (h2 : s 2 = false) (h12 : s 12 = false) (h14 : s 14 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[154]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h2, h12, h14]
  simp [h]

theorem color_witness_155 (s : Selection) (h0 : s 0 = false) (h12 : s 12 = false) (h14 : s 14 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[155]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h12, h14]
  simp [h]

theorem color_witness_156 (s : Selection) (h10 : s 10 = false) (h11 : s 11 = false) (h14 : s 14 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[156]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h10, h11, h14]
  simp [h]

theorem color_witness_157 (s : Selection) (h9 : s 9 = false) (h11 : s 11 = false) (h14 : s 14 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[157]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h9, h11, h14]
  simp [h]

theorem color_witness_158 (s : Selection) (h7 : s 7 = false) (h8 : s 8 = false) (h11 : s 11 = false) (h14 : s 14 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[158]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h7, h8, h11, h14]
  simp [h]

theorem color_witness_159 (s : Selection) (h6 : s 6 = false) (h8 : s 8 = false) (h10 : s 10 = false) (h14 : s 14 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[159]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h6, h8, h10, h14]
  simp [h]

theorem color_witness_160 (s : Selection) (h4 : s 4 = false) (h5 : s 5 = false) (h8 : s 8 = false) (h10 : s 10 = false) (h14 : s 14 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[160]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h4, h5, h8, h10, h14]
  simp [h]

theorem color_witness_161 (s : Selection) (h3 : s 3 = false) (h8 : s 8 = false) (h10 : s 10 = false) (h14 : s 14 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[161]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h3, h8, h10, h14]
  simp [h]

theorem color_witness_162 (s : Selection) (h1 : s 1 = false) (h2 : s 2 = false) (h8 : s 8 = false) (h10 : s 10 = false) (h14 : s 14 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[162]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h2, h8, h10, h14]
  simp [h]

theorem color_witness_163 (s : Selection) (h0 : s 0 = false) (h8 : s 8 = false) (h10 : s 10 = false) (h14 : s 14 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[163]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h8, h10, h14]
  simp [h]

theorem color_witness_164 (s : Selection) (h6 : s 6 = false) (h9 : s 9 = false) (h14 : s 14 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[164]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h6, h9, h14]
  simp [h]

theorem color_witness_165 (s : Selection) (h4 : s 4 = false) (h5 : s 5 = false) (h9 : s 9 = false) (h14 : s 14 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[165]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h4, h5, h9, h14]
  simp [h]

theorem color_witness_166 (s : Selection) (h3 : s 3 = false) (h9 : s 9 = false) (h14 : s 14 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[166]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h3, h9, h14]
  simp [h]

theorem color_witness_167 (s : Selection) (h1 : s 1 = false) (h2 : s 2 = false) (h9 : s 9 = false) (h14 : s 14 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[167]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h2, h9, h14]
  simp [h]

theorem color_witness_168 (s : Selection) (h0 : s 0 = false) (h9 : s 9 = false) (h14 : s 14 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[168]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h9, h14]
  simp [h]

theorem color_witness_169 (s : Selection) (h6 : s 6 = false) (h7 : s 7 = false) (h14 : s 14 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[169]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h6, h7, h14]
  simp [h]

theorem color_witness_170 (s : Selection) (h4 : s 4 = false) (h5 : s 5 = false) (h7 : s 7 = false) (h14 : s 14 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[170]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h4, h5, h7, h14]
  simp [h]

theorem color_witness_171 (s : Selection) (h3 : s 3 = false) (h7 : s 7 = false) (h14 : s 14 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[171]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h3, h7, h14]
  simp [h]

theorem color_witness_172 (s : Selection) (h1 : s 1 = false) (h2 : s 2 = false) (h7 : s 7 = false) (h14 : s 14 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[172]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h2, h7, h14]
  simp [h]

theorem color_witness_173 (s : Selection) (h0 : s 0 = false) (h7 : s 7 = false) (h14 : s 14 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[173]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h7, h14]
  simp [h]

theorem color_witness_174 (s : Selection) (h0 : s 0 = false) (h3 : s 3 = false) (h6 : s 6 = false) (h11 : s 11 = false) (h13 : s 13 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[174]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h3, h6, h11, h13]
  simp [h]

theorem color_witness_175 (s : Selection) (h2 : s 2 = false) (h6 : s 6 = false) (h11 : s 11 = false) (h13 : s 13 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[175]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h2, h6, h11, h13]
  simp [h]

theorem color_witness_176 (s : Selection) (h1 : s 1 = false) (h6 : s 6 = false) (h11 : s 11 = false) (h13 : s 13 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[176]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h6, h11, h13]
  simp [h]

theorem color_witness_177 (s : Selection) (h3 : s 3 = false) (h5 : s 5 = false) (h11 : s 11 = false) (h13 : s 13 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[177]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h3, h5, h11, h13]
  simp [h]

theorem color_witness_178 (s : Selection) (h0 : s 0 = false) (h2 : s 2 = false) (h5 : s 5 = false) (h11 : s 11 = false) (h13 : s 13 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[178]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h2, h5, h11, h13]
  simp [h]

theorem color_witness_179 (s : Selection) (h1 : s 1 = false) (h5 : s 5 = false) (h11 : s 11 = false) (h13 : s 13 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[179]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h5, h11, h13]
  simp [h]

theorem color_witness_180 (s : Selection) (h3 : s 3 = false) (h4 : s 4 = false) (h11 : s 11 = false) (h13 : s 13 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[180]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h3, h4, h11, h13]
  simp [h]

theorem color_witness_181 (s : Selection) (h2 : s 2 = false) (h4 : s 4 = false) (h11 : s 11 = false) (h13 : s 13 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[181]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h2, h4, h11, h13]
  simp [h]

theorem color_witness_182 (s : Selection) (h0 : s 0 = false) (h1 : s 1 = false) (h4 : s 4 = false) (h11 : s 11 = false) (h13 : s 13 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[182]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h1, h4, h11, h13]
  simp [h]

theorem color_witness_183 (s : Selection) (h5 : s 5 = false) (h7 : s 7 = false) (h10 : s 10 = false) (h13 : s 13 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[183]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h5, h7, h10, h13]
  simp [h]

theorem color_witness_184 (s : Selection) (h4 : s 4 = false) (h7 : s 7 = false) (h10 : s 10 = false) (h13 : s 13 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[184]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h4, h7, h10, h13]
  simp [h]

theorem color_witness_185 (s : Selection) (h2 : s 2 = false) (h7 : s 7 = false) (h10 : s 10 = false) (h13 : s 13 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[185]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h2, h7, h10, h13]
  simp [h]

theorem color_witness_186 (s : Selection) (h1 : s 1 = false) (h7 : s 7 = false) (h10 : s 10 = false) (h13 : s 13 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[186]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h7, h10, h13]
  simp [h]

theorem color_witness_187 (s : Selection) (h0 : s 0 = false) (h7 : s 7 = false) (h10 : s 10 = false) (h13 : s 13 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[187]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h7, h10, h13]
  simp [h]

theorem color_witness_188 (s : Selection) (h5 : s 5 = false) (h9 : s 9 = false) (h13 : s 13 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[188]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h5, h9, h13]
  simp [h]

theorem color_witness_189 (s : Selection) (h4 : s 4 = false) (h9 : s 9 = false) (h13 : s 13 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[189]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h4, h9, h13]
  simp [h]

theorem color_witness_190 (s : Selection) (h2 : s 2 = false) (h9 : s 9 = false) (h13 : s 13 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[190]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h2, h9, h13]
  simp [h]

theorem color_witness_191 (s : Selection) (h1 : s 1 = false) (h9 : s 9 = false) (h13 : s 13 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[191]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h9, h13]
  simp [h]

theorem color_witness_192 (s : Selection) (h0 : s 0 = false) (h9 : s 9 = false) (h13 : s 13 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[192]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h9, h13]
  simp [h]

theorem color_witness_193 (s : Selection) (h5 : s 5 = false) (h8 : s 8 = false) (h13 : s 13 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[193]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h5, h8, h13]
  simp [h]

theorem color_witness_194 (s : Selection) (h4 : s 4 = false) (h8 : s 8 = false) (h13 : s 13 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[194]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h4, h8, h13]
  simp [h]

theorem color_witness_195 (s : Selection) (h2 : s 2 = false) (h8 : s 8 = false) (h13 : s 13 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[195]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h2, h8, h13]
  simp [h]

theorem color_witness_196 (s : Selection) (h1 : s 1 = false) (h8 : s 8 = false) (h13 : s 13 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[196]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h8, h13]
  simp [h]

theorem color_witness_197 (s : Selection) (h0 : s 0 = false) (h8 : s 8 = false) (h13 : s 13 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[197]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h8, h13]
  simp [h]

theorem color_witness_198 (s : Selection) (h5 : s 5 = false) (h10 : s 10 = false) (h12 : s 12 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[198]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h5, h10, h12]
  simp [h]

theorem color_witness_199 (s : Selection) (h4 : s 4 = false) (h10 : s 10 = false) (h12 : s 12 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[199]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h4, h10, h12]
  simp [h]

theorem color_witness_200 (s : Selection) (h2 : s 2 = false) (h10 : s 10 = false) (h12 : s 12 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[200]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h2, h10, h12]
  simp [h]

theorem color_witness_201 (s : Selection) (h1 : s 1 = false) (h10 : s 10 = false) (h12 : s 12 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[201]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h10, h12]
  simp [h]

theorem color_witness_202 (s : Selection) (h0 : s 0 = false) (h10 : s 10 = false) (h12 : s 12 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[202]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h10, h12]
  simp [h]

theorem color_witness_203 (s : Selection) (h5 : s 5 = false) (h7 : s 7 = false) (h9 : s 9 = false) (h12 : s 12 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[203]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h5, h7, h9, h12]
  simp [h]

theorem color_witness_204 (s : Selection) (h4 : s 4 = false) (h7 : s 7 = false) (h9 : s 9 = false) (h12 : s 12 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[204]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h4, h7, h9, h12]
  simp [h]

theorem color_witness_205 (s : Selection) (h2 : s 2 = false) (h7 : s 7 = false) (h9 : s 9 = false) (h12 : s 12 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[205]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h2, h7, h9, h12]
  simp [h]

theorem color_witness_206 (s : Selection) (h1 : s 1 = false) (h7 : s 7 = false) (h9 : s 9 = false) (h12 : s 12 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[206]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h7, h9, h12]
  simp [h]

theorem color_witness_207 (s : Selection) (h0 : s 0 = false) (h7 : s 7 = false) (h9 : s 9 = false) (h12 : s 12 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[207]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h7, h9, h12]
  simp [h]

theorem color_witness_208 (s : Selection) (h5 : s 5 = false) (h8 : s 8 = false) (h12 : s 12 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[208]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h5, h8, h12]
  simp [h]

theorem color_witness_209 (s : Selection) (h4 : s 4 = false) (h8 : s 8 = false) (h12 : s 12 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[209]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h4, h8, h12]
  simp [h]

theorem color_witness_210 (s : Selection) (h2 : s 2 = false) (h8 : s 8 = false) (h12 : s 12 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[210]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h2, h8, h12]
  simp [h]

theorem color_witness_211 (s : Selection) (h1 : s 1 = false) (h8 : s 8 = false) (h12 : s 12 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[211]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h8, h12]
  simp [h]

theorem color_witness_212 (s : Selection) (h0 : s 0 = false) (h8 : s 8 = false) (h12 : s 12 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[212]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h8, h12]
  simp [h]

theorem color_witness_213 (s : Selection) (h0 : s 0 = false) (h3 : s 3 = false) (h6 : s 6 = false) (h12 : s 12 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[213]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h3, h6, h12]
  simp [h]

theorem color_witness_214 (s : Selection) (h2 : s 2 = false) (h6 : s 6 = false) (h12 : s 12 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[214]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h2, h6, h12]
  simp [h]

theorem color_witness_215 (s : Selection) (h1 : s 1 = false) (h6 : s 6 = false) (h12 : s 12 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[215]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h6, h12]
  simp [h]

theorem color_witness_216 (s : Selection) (h3 : s 3 = false) (h5 : s 5 = false) (h12 : s 12 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[216]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h3, h5, h12]
  simp [h]

theorem color_witness_217 (s : Selection) (h0 : s 0 = false) (h2 : s 2 = false) (h5 : s 5 = false) (h12 : s 12 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[217]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h2, h5, h12]
  simp [h]

theorem color_witness_218 (s : Selection) (h1 : s 1 = false) (h5 : s 5 = false) (h12 : s 12 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[218]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h5, h12]
  simp [h]

theorem color_witness_219 (s : Selection) (h3 : s 3 = false) (h4 : s 4 = false) (h12 : s 12 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[219]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h3, h4, h12]
  simp [h]

theorem color_witness_220 (s : Selection) (h2 : s 2 = false) (h4 : s 4 = false) (h12 : s 12 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[220]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h2, h4, h12]
  simp [h]

theorem color_witness_221 (s : Selection) (h0 : s 0 = false) (h1 : s 1 = false) (h4 : s 4 = false) (h12 : s 12 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[221]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h1, h4, h12]
  simp [h]

theorem color_witness_222 (s : Selection) (h5 : s 5 = false) (h10 : s 10 = false) (h11 : s 11 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[222]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h5, h10, h11]
  simp [h]

theorem color_witness_223 (s : Selection) (h4 : s 4 = false) (h10 : s 10 = false) (h11 : s 11 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[223]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h4, h10, h11]
  simp [h]

theorem color_witness_224 (s : Selection) (h2 : s 2 = false) (h10 : s 10 = false) (h11 : s 11 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[224]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h2, h10, h11]
  simp [h]

theorem color_witness_225 (s : Selection) (h1 : s 1 = false) (h10 : s 10 = false) (h11 : s 11 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[225]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h10, h11]
  simp [h]

theorem color_witness_226 (s : Selection) (h0 : s 0 = false) (h10 : s 10 = false) (h11 : s 11 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[226]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h10, h11]
  simp [h]

theorem color_witness_227 (s : Selection) (h5 : s 5 = false) (h9 : s 9 = false) (h11 : s 11 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[227]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h5, h9, h11]
  simp [h]

theorem color_witness_228 (s : Selection) (h4 : s 4 = false) (h9 : s 9 = false) (h11 : s 11 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[228]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h4, h9, h11]
  simp [h]

theorem color_witness_229 (s : Selection) (h2 : s 2 = false) (h9 : s 9 = false) (h11 : s 11 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[229]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h2, h9, h11]
  simp [h]

theorem color_witness_230 (s : Selection) (h1 : s 1 = false) (h9 : s 9 = false) (h11 : s 11 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[230]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h9, h11]
  simp [h]

theorem color_witness_231 (s : Selection) (h0 : s 0 = false) (h9 : s 9 = false) (h11 : s 11 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[231]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h9, h11]
  simp [h]

theorem color_witness_232 (s : Selection) (h5 : s 5 = false) (h7 : s 7 = false) (h8 : s 8 = false) (h11 : s 11 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[232]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h5, h7, h8, h11]
  simp [h]

theorem color_witness_233 (s : Selection) (h4 : s 4 = false) (h7 : s 7 = false) (h8 : s 8 = false) (h11 : s 11 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[233]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h4, h7, h8, h11]
  simp [h]

theorem color_witness_234 (s : Selection) (h2 : s 2 = false) (h7 : s 7 = false) (h8 : s 8 = false) (h11 : s 11 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[234]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h2, h7, h8, h11]
  simp [h]

theorem color_witness_235 (s : Selection) (h1 : s 1 = false) (h7 : s 7 = false) (h8 : s 8 = false) (h11 : s 11 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[235]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h7, h8, h11]
  simp [h]

theorem color_witness_236 (s : Selection) (h0 : s 0 = false) (h7 : s 7 = false) (h8 : s 8 = false) (h11 : s 11 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[236]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h7, h8, h11]
  simp [h]

theorem color_witness_237 (s : Selection) (h0 : s 0 = false) (h3 : s 3 = false) (h6 : s 6 = false) (h8 : s 8 = false) (h10 : s 10 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[237]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h3, h6, h8, h10]
  simp [h]

theorem color_witness_238 (s : Selection) (h2 : s 2 = false) (h6 : s 6 = false) (h8 : s 8 = false) (h10 : s 10 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[238]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h2, h6, h8, h10]
  simp [h]

theorem color_witness_239 (s : Selection) (h1 : s 1 = false) (h6 : s 6 = false) (h8 : s 8 = false) (h10 : s 10 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[239]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h6, h8, h10]
  simp [h]

theorem color_witness_240 (s : Selection) (h3 : s 3 = false) (h5 : s 5 = false) (h8 : s 8 = false) (h10 : s 10 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[240]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h3, h5, h8, h10]
  simp [h]

theorem color_witness_241 (s : Selection) (h0 : s 0 = false) (h2 : s 2 = false) (h5 : s 5 = false) (h8 : s 8 = false) (h10 : s 10 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[241]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h2, h5, h8, h10]
  simp [h]

theorem color_witness_242 (s : Selection) (h1 : s 1 = false) (h5 : s 5 = false) (h8 : s 8 = false) (h10 : s 10 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[242]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h5, h8, h10]
  simp [h]

theorem color_witness_243 (s : Selection) (h3 : s 3 = false) (h4 : s 4 = false) (h8 : s 8 = false) (h10 : s 10 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[243]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h3, h4, h8, h10]
  simp [h]

theorem color_witness_244 (s : Selection) (h2 : s 2 = false) (h4 : s 4 = false) (h8 : s 8 = false) (h10 : s 10 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[244]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h2, h4, h8, h10]
  simp [h]

theorem color_witness_245 (s : Selection) (h0 : s 0 = false) (h1 : s 1 = false) (h4 : s 4 = false) (h8 : s 8 = false) (h10 : s 10 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[245]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h1, h4, h8, h10]
  simp [h]

theorem color_witness_246 (s : Selection) (h0 : s 0 = false) (h3 : s 3 = false) (h6 : s 6 = false) (h9 : s 9 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[246]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h3, h6, h9]
  simp [h]

theorem color_witness_247 (s : Selection) (h2 : s 2 = false) (h6 : s 6 = false) (h9 : s 9 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[247]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h2, h6, h9]
  simp [h]

theorem color_witness_248 (s : Selection) (h1 : s 1 = false) (h6 : s 6 = false) (h9 : s 9 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[248]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h6, h9]
  simp [h]

theorem color_witness_249 (s : Selection) (h3 : s 3 = false) (h5 : s 5 = false) (h9 : s 9 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[249]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h3, h5, h9]
  simp [h]

theorem color_witness_250 (s : Selection) (h0 : s 0 = false) (h2 : s 2 = false) (h5 : s 5 = false) (h9 : s 9 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[250]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h2, h5, h9]
  simp [h]

theorem color_witness_251 (s : Selection) (h1 : s 1 = false) (h5 : s 5 = false) (h9 : s 9 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[251]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h5, h9]
  simp [h]

theorem color_witness_252 (s : Selection) (h3 : s 3 = false) (h4 : s 4 = false) (h9 : s 9 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[252]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h3, h4, h9]
  simp [h]

theorem color_witness_253 (s : Selection) (h2 : s 2 = false) (h4 : s 4 = false) (h9 : s 9 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[253]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h2, h4, h9]
  simp [h]

theorem color_witness_254 (s : Selection) (h0 : s 0 = false) (h1 : s 1 = false) (h4 : s 4 = false) (h9 : s 9 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[254]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h1, h4, h9]
  simp [h]

theorem color_witness_255 (s : Selection) (h0 : s 0 = false) (h3 : s 3 = false) (h6 : s 6 = false) (h7 : s 7 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[255]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h3, h6, h7]
  simp [h]

theorem color_witness_256 (s : Selection) (h2 : s 2 = false) (h6 : s 6 = false) (h7 : s 7 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[256]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h2, h6, h7]
  simp [h]

theorem color_witness_257 (s : Selection) (h1 : s 1 = false) (h6 : s 6 = false) (h7 : s 7 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[257]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h6, h7]
  simp [h]

theorem color_witness_258 (s : Selection) (h3 : s 3 = false) (h5 : s 5 = false) (h7 : s 7 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[258]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h3, h5, h7]
  simp [h]

theorem color_witness_259 (s : Selection) (h0 : s 0 = false) (h2 : s 2 = false) (h5 : s 5 = false) (h7 : s 7 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[259]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h2, h5, h7]
  simp [h]

theorem color_witness_260 (s : Selection) (h1 : s 1 = false) (h5 : s 5 = false) (h7 : s 7 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[260]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h1, h5, h7]
  simp [h]

theorem color_witness_261 (s : Selection) (h3 : s 3 = false) (h4 : s 4 = false) (h7 : s 7 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[261]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h3, h4, h7]
  simp [h]

theorem color_witness_262 (s : Selection) (h2 : s 2 = false) (h4 : s 4 = false) (h7 : s 7 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[262]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h2, h4, h7]
  simp [h]

theorem color_witness_263 (s : Selection) (h0 : s 0 = false) (h1 : s 1 = false) (h4 : s 4 = false) (h7 : s 7 = false) :
    (corePresent s || coverAvailable s) = true := by
  have h : coverAvailable s = true := by
    apply List.any_eq_true.mpr
    refine ⟨coverCertificates[263]'(by decide), ?_, ?_⟩
    · exact List.getElem_mem (by decide)
    · simp [ThreeColorCertificate.Permitted,
        coverCertificates, h0, h1, h4, h7]
  simp [h]

theorem every_selection_covered (s : Selection) :
    (corePresent s || coverAvailable s) = true := by
  cases h7 : s 7 with
  | false =>
    cases h9 : s 9 with
    | false =>
      cases h0 : s 0 with
      | false =>
        cases h12 : s 12 with
        | false =>
          exact color_witness_207 s h0 h7 h9 h12
        | true =>
          cases h14 : s 14 with
          | false =>
            exact color_witness_168 s h0 h9 h14
          | true =>
            cases h1 : s 1 with
            | false =>
              cases h4 : s 4 with
              | false =>
                exact color_witness_254 s h0 h1 h4 h9
              | true =>
                cases h5 : s 5 with
                | false =>
                  exact color_witness_251 s h1 h5 h9
                | true =>
                  cases h2 : s 2 with
                  | false =>
                    cases h11 : s 11 with
                    | false =>
                      exact color_witness_229 s h2 h9 h11
                    | true =>
                      cases h17 : s 17 with
                      | false =>
                        exact color_witness_82 s h2 h7 h17
                      | true =>
                        cases h13 : s 13 with
                        | false =>
                          exact color_witness_190 s h2 h9 h13
                        | true =>
                          cases h18 : s 18 with
                          | false =>
                            exact color_witness_52 s h2 h7 h18
                          | true =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_247 s h2 h6 h9
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_133 s h2 h9 h15
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_108 s h1 h9 h16
                                | true =>
                                  exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
                  | true =>
                    cases h11 : s 11 with
                    | false =>
                      exact color_witness_230 s h1 h9 h11
                    | true =>
                      cases h17 : s 17 with
                      | false =>
                        exact color_witness_83 s h1 h7 h17
                      | true =>
                        cases h16 : s 16 with
                        | false =>
                          exact color_witness_108 s h1 h9 h16
                        | true =>
                          cases h13 : s 13 with
                          | false =>
                            exact color_witness_191 s h1 h9 h13
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_53 s h1 h7 h18
                            | true =>
                              cases h6 : s 6 with
                              | false =>
                                exact color_witness_248 s h1 h6 h9
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  exact color_witness_134 s h0 h9 h15
                                | true =>
                                  exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
            | true =>
              cases h2 : s 2 with
              | false =>
                cases h4 : s 4 with
                | false =>
                  exact color_witness_253 s h2 h4 h9
                | true =>
                  cases h5 : s 5 with
                  | false =>
                    exact color_witness_250 s h0 h2 h5 h9
                  | true =>
                    cases h11 : s 11 with
                    | false =>
                      exact color_witness_229 s h2 h9 h11
                    | true =>
                      cases h17 : s 17 with
                      | false =>
                        exact color_witness_82 s h2 h7 h17
                      | true =>
                        cases h15 : s 15 with
                        | false =>
                          exact color_witness_133 s h2 h9 h15
                        | true =>
                          cases h13 : s 13 with
                          | false =>
                            exact color_witness_190 s h2 h9 h13
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_52 s h2 h7 h18
                            | true =>
                              cases h6 : s 6 with
                              | false =>
                                exact color_witness_247 s h2 h6 h9
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_109 s h0 h9 h16
                                | true =>
                                  exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
              | true =>
                cases h4 : s 4 with
                | false =>
                  cases h5 : s 5 with
                  | false =>
                    cases h11 : s 11 with
                    | false =>
                      exact color_witness_227 s h5 h9 h11
                    | true =>
                      cases h17 : s 17 with
                      | false =>
                        exact color_witness_80 s h5 h7 h17
                      | true =>
                        cases h13 : s 13 with
                        | false =>
                          exact color_witness_188 s h5 h9 h13
                        | true =>
                          cases h18 : s 18 with
                          | false =>
                            exact color_witness_50 s h5 h7 h18
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_249 s h3 h5 h9
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_131 s h5 h9 h15
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_106 s h4 h9 h16
                                | true =>
                                  exact core_witness_11 s h1 h2 h3 h11 h12 h13 h14 h15 h16 h17 h18
                  | true =>
                    cases h11 : s 11 with
                    | false =>
                      exact color_witness_228 s h4 h9 h11
                    | true =>
                      cases h17 : s 17 with
                      | false =>
                        exact color_witness_81 s h4 h7 h17
                      | true =>
                        cases h16 : s 16 with
                        | false =>
                          exact color_witness_106 s h4 h9 h16
                        | true =>
                          cases h13 : s 13 with
                          | false =>
                            exact color_witness_189 s h4 h9 h13
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_51 s h4 h7 h18
                            | true =>
                              cases h3 : s 3 with
                              | false =>
                                exact color_witness_252 s h3 h4 h9
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  exact color_witness_134 s h0 h9 h15
                                | true =>
                                  exact core_witness_11 s h1 h2 h3 h11 h12 h13 h14 h15 h16 h17 h18
                | true =>
                  cases h5 : s 5 with
                  | false =>
                    cases h11 : s 11 with
                    | false =>
                      exact color_witness_227 s h5 h9 h11
                    | true =>
                      cases h17 : s 17 with
                      | false =>
                        exact color_witness_80 s h5 h7 h17
                      | true =>
                        cases h15 : s 15 with
                        | false =>
                          exact color_witness_131 s h5 h9 h15
                        | true =>
                          cases h13 : s 13 with
                          | false =>
                            exact color_witness_188 s h5 h9 h13
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_50 s h5 h7 h18
                            | true =>
                              cases h3 : s 3 with
                              | false =>
                                exact color_witness_249 s h3 h5 h9
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_109 s h0 h9 h16
                                | true =>
                                  exact core_witness_11 s h1 h2 h3 h11 h12 h13 h14 h15 h16 h17 h18
                  | true =>
                    cases h11 : s 11 with
                    | false =>
                      exact color_witness_231 s h0 h9 h11
                    | true =>
                      cases h17 : s 17 with
                      | false =>
                        exact color_witness_84 s h0 h7 h17
                      | true =>
                        cases h15 : s 15 with
                        | false =>
                          exact color_witness_134 s h0 h9 h15
                        | true =>
                          cases h16 : s 16 with
                          | false =>
                            exact color_witness_109 s h0 h9 h16
                          | true =>
                            cases h13 : s 13 with
                            | false =>
                              exact color_witness_192 s h0 h9 h13
                            | true =>
                              cases h18 : s 18 with
                              | false =>
                                exact color_witness_54 s h0 h7 h18
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_246 s h0 h3 h6 h9
                                  | true =>
                                    exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
                                | true =>
                                  exact core_witness_11 s h1 h2 h3 h11 h12 h13 h14 h15 h16 h17 h18
      | true =>
        cases h1 : s 1 with
        | false =>
          cases h5 : s 5 with
          | false =>
            exact color_witness_251 s h1 h5 h9
          | true =>
            cases h2 : s 2 with
            | false =>
              cases h4 : s 4 with
              | false =>
                exact color_witness_253 s h2 h4 h9
              | true =>
                cases h14 : s 14 with
                | false =>
                  exact color_witness_167 s h1 h2 h9 h14
                | true =>
                  cases h12 : s 12 with
                  | false =>
                    exact color_witness_205 s h2 h7 h9 h12
                  | true =>
                    cases h11 : s 11 with
                    | false =>
                      exact color_witness_229 s h2 h9 h11
                    | true =>
                      cases h17 : s 17 with
                      | false =>
                        exact color_witness_82 s h2 h7 h17
                      | true =>
                        cases h6 : s 6 with
                        | false =>
                          exact color_witness_247 s h2 h6 h9
                        | true =>
                          cases h13 : s 13 with
                          | false =>
                            exact color_witness_190 s h2 h9 h13
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_52 s h2 h7 h18
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_133 s h2 h9 h15
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_108 s h1 h9 h16
                                | true =>
                                  exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
            | true =>
              cases h4 : s 4 with
              | false =>
                cases h14 : s 14 with
                | false =>
                  cases h12 : s 12 with
                  | false =>
                    exact color_witness_149 s h7 h9 h12 h14
                  | true =>
                    cases h11 : s 11 with
                    | false =>
                      exact color_witness_157 s h9 h11 h14
                    | true =>
                      cases h17 : s 17 with
                      | false =>
                        exact color_witness_59 s h7 h14 h17
                      | true =>
                        cases h13 : s 13 with
                        | false =>
                          exact color_witness_146 s h9 h13 h14
                        | true =>
                          cases h18 : s 18 with
                          | false =>
                            exact color_witness_29 s h7 h14 h18
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_166 s h3 h9 h14
                            | true =>
                              cases h6 : s 6 with
                              | false =>
                                exact color_witness_164 s h6 h9 h14
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_106 s h4 h9 h16
                                | true =>
                                  exact core_witness_8 s h0 h2 h3 h5 h6 h11 h12 h13 h16 h17 h18
                | true =>
                  cases h12 : s 12 with
                  | false =>
                    exact color_witness_204 s h4 h7 h9 h12
                  | true =>
                    cases h11 : s 11 with
                    | false =>
                      exact color_witness_228 s h4 h9 h11
                    | true =>
                      cases h17 : s 17 with
                      | false =>
                        exact color_witness_81 s h4 h7 h17
                      | true =>
                        cases h16 : s 16 with
                        | false =>
                          exact color_witness_106 s h4 h9 h16
                        | true =>
                          cases h13 : s 13 with
                          | false =>
                            exact color_witness_189 s h4 h9 h13
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_51 s h4 h7 h18
                            | true =>
                              cases h3 : s 3 with
                              | false =>
                                exact color_witness_252 s h3 h4 h9
                              | true =>
                                cases h6 : s 6 with
                                | false =>
                                  exact color_witness_248 s h1 h6 h9
                                | true =>
                                  exact core_witness_8 s h0 h2 h3 h5 h6 h11 h12 h13 h16 h17 h18
              | true =>
                cases h14 : s 14 with
                | false =>
                  cases h12 : s 12 with
                  | false =>
                    exact color_witness_149 s h7 h9 h12 h14
                  | true =>
                    cases h11 : s 11 with
                    | false =>
                      exact color_witness_157 s h9 h11 h14
                    | true =>
                      cases h17 : s 17 with
                      | false =>
                        exact color_witness_59 s h7 h14 h17
                      | true =>
                        cases h6 : s 6 with
                        | false =>
                          exact color_witness_164 s h6 h9 h14
                        | true =>
                          cases h13 : s 13 with
                          | false =>
                            exact color_witness_146 s h9 h13 h14
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_29 s h7 h14 h18
                            | true =>
                              cases h3 : s 3 with
                              | false =>
                                exact color_witness_166 s h3 h9 h14
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_108 s h1 h9 h16
                                | true =>
                                  exact core_witness_8 s h0 h2 h3 h5 h6 h11 h12 h13 h16 h17 h18
                | true =>
                  cases h12 : s 12 with
                  | false =>
                    exact color_witness_206 s h1 h7 h9 h12
                  | true =>
                    cases h11 : s 11 with
                    | false =>
                      exact color_witness_230 s h1 h9 h11
                    | true =>
                      cases h17 : s 17 with
                      | false =>
                        exact color_witness_83 s h1 h7 h17
                      | true =>
                        cases h6 : s 6 with
                        | false =>
                          exact color_witness_248 s h1 h6 h9
                        | true =>
                          cases h16 : s 16 with
                          | false =>
                            exact color_witness_108 s h1 h9 h16
                          | true =>
                            cases h13 : s 13 with
                            | false =>
                              exact color_witness_191 s h1 h9 h13
                            | true =>
                              cases h18 : s 18 with
                              | false =>
                                exact color_witness_53 s h1 h7 h18
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_132 s h1 h3 h9 h15
                                  | true =>
                                    exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
                                | true =>
                                  exact core_witness_8 s h0 h2 h3 h5 h6 h11 h12 h13 h16 h17 h18
        | true =>
          cases h4 : s 4 with
          | false =>
            cases h2 : s 2 with
            | false =>
              exact color_witness_253 s h2 h4 h9
            | true =>
              cases h5 : s 5 with
              | false =>
                cases h14 : s 14 with
                | false =>
                  exact color_witness_165 s h4 h5 h9 h14
                | true =>
                  cases h12 : s 12 with
                  | false =>
                    exact color_witness_203 s h5 h7 h9 h12
                  | true =>
                    cases h11 : s 11 with
                    | false =>
                      exact color_witness_227 s h5 h9 h11
                    | true =>
                      cases h17 : s 17 with
                      | false =>
                        exact color_witness_80 s h5 h7 h17
                      | true =>
                        cases h3 : s 3 with
                        | false =>
                          exact color_witness_249 s h3 h5 h9
                        | true =>
                          cases h13 : s 13 with
                          | false =>
                            exact color_witness_188 s h5 h9 h13
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_50 s h5 h7 h18
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_131 s h5 h9 h15
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_106 s h4 h9 h16
                                | true =>
                                  exact core_witness_11 s h1 h2 h3 h11 h12 h13 h14 h15 h16 h17 h18
              | true =>
                cases h14 : s 14 with
                | false =>
                  cases h12 : s 12 with
                  | false =>
                    exact color_witness_149 s h7 h9 h12 h14
                  | true =>
                    cases h11 : s 11 with
                    | false =>
                      exact color_witness_157 s h9 h11 h14
                    | true =>
                      cases h17 : s 17 with
                      | false =>
                        exact color_witness_59 s h7 h14 h17
                      | true =>
                        cases h3 : s 3 with
                        | false =>
                          exact color_witness_166 s h3 h9 h14
                        | true =>
                          cases h13 : s 13 with
                          | false =>
                            exact color_witness_146 s h9 h13 h14
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_29 s h7 h14 h18
                            | true =>
                              cases h6 : s 6 with
                              | false =>
                                exact color_witness_164 s h6 h9 h14
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_106 s h4 h9 h16
                                | true =>
                                  exact core_witness_8 s h0 h2 h3 h5 h6 h11 h12 h13 h16 h17 h18
                | true =>
                  cases h12 : s 12 with
                  | false =>
                    exact color_witness_204 s h4 h7 h9 h12
                  | true =>
                    cases h11 : s 11 with
                    | false =>
                      exact color_witness_228 s h4 h9 h11
                    | true =>
                      cases h17 : s 17 with
                      | false =>
                        exact color_witness_81 s h4 h7 h17
                      | true =>
                        cases h3 : s 3 with
                        | false =>
                          exact color_witness_252 s h3 h4 h9
                        | true =>
                          cases h16 : s 16 with
                          | false =>
                            exact color_witness_106 s h4 h9 h16
                          | true =>
                            cases h13 : s 13 with
                            | false =>
                              exact color_witness_189 s h4 h9 h13
                            | true =>
                              cases h18 : s 18 with
                              | false =>
                                exact color_witness_51 s h4 h7 h18
                              | true =>
                                cases h6 : s 6 with
                                | false =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_130 s h4 h6 h9 h15
                                  | true =>
                                    exact core_witness_11 s h1 h2 h3 h11 h12 h13 h14 h15 h16 h17 h18
                                | true =>
                                  exact core_witness_8 s h0 h2 h3 h5 h6 h11 h12 h13 h16 h17 h18
          | true =>
            cases h2 : s 2 with
            | false =>
              cases h5 : s 5 with
              | false =>
                cases h14 : s 14 with
                | false =>
                  cases h12 : s 12 with
                  | false =>
                    exact color_witness_149 s h7 h9 h12 h14
                  | true =>
                    cases h11 : s 11 with
                    | false =>
                      exact color_witness_157 s h9 h11 h14
                    | true =>
                      cases h17 : s 17 with
                      | false =>
                        exact color_witness_59 s h7 h14 h17
                      | true =>
                        cases h13 : s 13 with
                        | false =>
                          exact color_witness_146 s h9 h13 h14
                        | true =>
                          cases h18 : s 18 with
                          | false =>
                            exact color_witness_29 s h7 h14 h18
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_166 s h3 h9 h14
                            | true =>
                              cases h6 : s 6 with
                              | false =>
                                exact color_witness_164 s h6 h9 h14
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  exact color_witness_131 s h5 h9 h15
                                | true =>
                                  exact core_witness_5 s h0 h1 h3 h4 h6 h11 h12 h13 h15 h17 h18
                | true =>
                  cases h12 : s 12 with
                  | false =>
                    exact color_witness_203 s h5 h7 h9 h12
                  | true =>
                    cases h11 : s 11 with
                    | false =>
                      exact color_witness_227 s h5 h9 h11
                    | true =>
                      cases h17 : s 17 with
                      | false =>
                        exact color_witness_80 s h5 h7 h17
                      | true =>
                        cases h15 : s 15 with
                        | false =>
                          exact color_witness_131 s h5 h9 h15
                        | true =>
                          cases h13 : s 13 with
                          | false =>
                            exact color_witness_188 s h5 h9 h13
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_50 s h5 h7 h18
                            | true =>
                              cases h3 : s 3 with
                              | false =>
                                exact color_witness_249 s h3 h5 h9
                              | true =>
                                cases h6 : s 6 with
                                | false =>
                                  exact color_witness_247 s h2 h6 h9
                                | true =>
                                  exact core_witness_5 s h0 h1 h3 h4 h6 h11 h12 h13 h15 h17 h18
              | true =>
                cases h14 : s 14 with
                | false =>
                  cases h12 : s 12 with
                  | false =>
                    exact color_witness_149 s h7 h9 h12 h14
                  | true =>
                    cases h11 : s 11 with
                    | false =>
                      exact color_witness_157 s h9 h11 h14
                    | true =>
                      cases h17 : s 17 with
                      | false =>
                        exact color_witness_59 s h7 h14 h17
                      | true =>
                        cases h6 : s 6 with
                        | false =>
                          exact color_witness_164 s h6 h9 h14
                        | true =>
                          cases h13 : s 13 with
                          | false =>
                            exact color_witness_146 s h9 h13 h14
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_29 s h7 h14 h18
                            | true =>
                              cases h3 : s 3 with
                              | false =>
                                exact color_witness_166 s h3 h9 h14
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  exact color_witness_133 s h2 h9 h15
                                | true =>
                                  exact core_witness_5 s h0 h1 h3 h4 h6 h11 h12 h13 h15 h17 h18
                | true =>
                  cases h12 : s 12 with
                  | false =>
                    exact color_witness_205 s h2 h7 h9 h12
                  | true =>
                    cases h11 : s 11 with
                    | false =>
                      exact color_witness_229 s h2 h9 h11
                    | true =>
                      cases h17 : s 17 with
                      | false =>
                        exact color_witness_82 s h2 h7 h17
                      | true =>
                        cases h6 : s 6 with
                        | false =>
                          exact color_witness_247 s h2 h6 h9
                        | true =>
                          cases h15 : s 15 with
                          | false =>
                            exact color_witness_133 s h2 h9 h15
                          | true =>
                            cases h13 : s 13 with
                            | false =>
                              exact color_witness_190 s h2 h9 h13
                            | true =>
                              cases h18 : s 18 with
                              | false =>
                                exact color_witness_52 s h2 h7 h18
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  cases h16 : s 16 with
                                  | false =>
                                    exact color_witness_107 s h2 h3 h9 h16
                                  | true =>
                                    exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
                                | true =>
                                  exact core_witness_5 s h0 h1 h3 h4 h6 h11 h12 h13 h15 h17 h18
            | true =>
              cases h5 : s 5 with
              | false =>
                cases h14 : s 14 with
                | false =>
                  cases h12 : s 12 with
                  | false =>
                    exact color_witness_149 s h7 h9 h12 h14
                  | true =>
                    cases h11 : s 11 with
                    | false =>
                      exact color_witness_157 s h9 h11 h14
                    | true =>
                      cases h17 : s 17 with
                      | false =>
                        exact color_witness_59 s h7 h14 h17
                      | true =>
                        cases h3 : s 3 with
                        | false =>
                          exact color_witness_166 s h3 h9 h14
                        | true =>
                          cases h13 : s 13 with
                          | false =>
                            exact color_witness_146 s h9 h13 h14
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_29 s h7 h14 h18
                            | true =>
                              cases h6 : s 6 with
                              | false =>
                                exact color_witness_164 s h6 h9 h14
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  exact color_witness_131 s h5 h9 h15
                                | true =>
                                  exact core_witness_5 s h0 h1 h3 h4 h6 h11 h12 h13 h15 h17 h18
                | true =>
                  cases h12 : s 12 with
                  | false =>
                    exact color_witness_203 s h5 h7 h9 h12
                  | true =>
                    cases h11 : s 11 with
                    | false =>
                      exact color_witness_227 s h5 h9 h11
                    | true =>
                      cases h17 : s 17 with
                      | false =>
                        exact color_witness_80 s h5 h7 h17
                      | true =>
                        cases h3 : s 3 with
                        | false =>
                          exact color_witness_249 s h3 h5 h9
                        | true =>
                          cases h15 : s 15 with
                          | false =>
                            exact color_witness_131 s h5 h9 h15
                          | true =>
                            cases h13 : s 13 with
                            | false =>
                              exact color_witness_188 s h5 h9 h13
                            | true =>
                              cases h18 : s 18 with
                              | false =>
                                exact color_witness_50 s h5 h7 h18
                              | true =>
                                cases h6 : s 6 with
                                | false =>
                                  cases h16 : s 16 with
                                  | false =>
                                    exact color_witness_105 s h5 h6 h9 h16
                                  | true =>
                                    exact core_witness_11 s h1 h2 h3 h11 h12 h13 h14 h15 h16 h17 h18
                                | true =>
                                  exact core_witness_5 s h0 h1 h3 h4 h6 h11 h12 h13 h15 h17 h18
              | true =>
                cases h14 : s 14 with
                | false =>
                  cases h12 : s 12 with
                  | false =>
                    exact color_witness_149 s h7 h9 h12 h14
                  | true =>
                    cases h11 : s 11 with
                    | false =>
                      exact color_witness_157 s h9 h11 h14
                    | true =>
                      cases h17 : s 17 with
                      | false =>
                        exact color_witness_59 s h7 h14 h17
                      | true =>
                        cases h3 : s 3 with
                        | false =>
                          exact color_witness_166 s h3 h9 h14
                        | true =>
                          cases h6 : s 6 with
                          | false =>
                            exact color_witness_164 s h6 h9 h14
                          | true =>
                            cases h13 : s 13 with
                            | false =>
                              exact color_witness_146 s h9 h13 h14
                            | true =>
                              cases h18 : s 18 with
                              | false =>
                                exact color_witness_29 s h7 h14 h18
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  cases h16 : s 16 with
                                  | false =>
                                    exact color_witness_88 s h9 h14 h15 h16
                                  | true =>
                                    exact core_witness_8 s h0 h2 h3 h5 h6 h11 h12 h13 h16 h17 h18
                                | true =>
                                  exact core_witness_5 s h0 h1 h3 h4 h6 h11 h12 h13 h15 h17 h18
                | true =>
                  exact core_witness_0 s h0 h1 h2 h4 h5 h14
    | true =>
      cases h12 : s 12 with
      | false =>
        cases h0 : s 0 with
        | false =>
          cases h14 : s 14 with
          | false =>
            exact color_witness_155 s h0 h12 h14
          | true =>
            cases h1 : s 1 with
            | false =>
              cases h4 : s 4 with
              | false =>
                exact color_witness_221 s h0 h1 h4 h12
              | true =>
                cases h5 : s 5 with
                | false =>
                  exact color_witness_218 s h1 h5 h12
                | true =>
                  cases h2 : s 2 with
                  | false =>
                    cases h8 : s 8 with
                    | false =>
                      exact color_witness_210 s h2 h8 h12
                    | true =>
                      cases h17 : s 17 with
                      | false =>
                        exact color_witness_82 s h2 h7 h17
                      | true =>
                        cases h10 : s 10 with
                        | false =>
                          exact color_witness_200 s h2 h10 h12
                        | true =>
                          cases h18 : s 18 with
                          | false =>
                            exact color_witness_52 s h2 h7 h18
                          | true =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_214 s h2 h6 h12
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_123 s h2 h12 h15
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_98 s h1 h12 h16
                                | true =>
                                  exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
                  | true =>
                    cases h8 : s 8 with
                    | false =>
                      exact color_witness_211 s h1 h8 h12
                    | true =>
                      cases h17 : s 17 with
                      | false =>
                        exact color_witness_83 s h1 h7 h17
                      | true =>
                        cases h16 : s 16 with
                        | false =>
                          exact color_witness_98 s h1 h12 h16
                        | true =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_201 s h1 h10 h12
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_53 s h1 h7 h18
                            | true =>
                              cases h6 : s 6 with
                              | false =>
                                exact color_witness_215 s h1 h6 h12
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  exact color_witness_124 s h0 h12 h15
                                | true =>
                                  exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
            | true =>
              cases h2 : s 2 with
              | false =>
                cases h4 : s 4 with
                | false =>
                  exact color_witness_220 s h2 h4 h12
                | true =>
                  cases h5 : s 5 with
                  | false =>
                    exact color_witness_217 s h0 h2 h5 h12
                  | true =>
                    cases h8 : s 8 with
                    | false =>
                      exact color_witness_210 s h2 h8 h12
                    | true =>
                      cases h17 : s 17 with
                      | false =>
                        exact color_witness_82 s h2 h7 h17
                      | true =>
                        cases h15 : s 15 with
                        | false =>
                          exact color_witness_123 s h2 h12 h15
                        | true =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_200 s h2 h10 h12
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_52 s h2 h7 h18
                            | true =>
                              cases h6 : s 6 with
                              | false =>
                                exact color_witness_214 s h2 h6 h12
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_99 s h0 h12 h16
                                | true =>
                                  exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
              | true =>
                cases h4 : s 4 with
                | false =>
                  cases h5 : s 5 with
                  | false =>
                    cases h8 : s 8 with
                    | false =>
                      exact color_witness_208 s h5 h8 h12
                    | true =>
                      cases h17 : s 17 with
                      | false =>
                        exact color_witness_80 s h5 h7 h17
                      | true =>
                        cases h10 : s 10 with
                        | false =>
                          exact color_witness_198 s h5 h10 h12
                        | true =>
                          cases h18 : s 18 with
                          | false =>
                            exact color_witness_50 s h5 h7 h18
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_216 s h3 h5 h12
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_121 s h5 h12 h15
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_96 s h4 h12 h16
                                | true =>
                                  exact core_witness_10 s h1 h2 h3 h8 h9 h10 h14 h15 h16 h17 h18
                  | true =>
                    cases h8 : s 8 with
                    | false =>
                      exact color_witness_209 s h4 h8 h12
                    | true =>
                      cases h17 : s 17 with
                      | false =>
                        exact color_witness_81 s h4 h7 h17
                      | true =>
                        cases h16 : s 16 with
                        | false =>
                          exact color_witness_96 s h4 h12 h16
                        | true =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_199 s h4 h10 h12
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_51 s h4 h7 h18
                            | true =>
                              cases h3 : s 3 with
                              | false =>
                                exact color_witness_219 s h3 h4 h12
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  exact color_witness_124 s h0 h12 h15
                                | true =>
                                  exact core_witness_10 s h1 h2 h3 h8 h9 h10 h14 h15 h16 h17 h18
                | true =>
                  cases h5 : s 5 with
                  | false =>
                    cases h8 : s 8 with
                    | false =>
                      exact color_witness_208 s h5 h8 h12
                    | true =>
                      cases h17 : s 17 with
                      | false =>
                        exact color_witness_80 s h5 h7 h17
                      | true =>
                        cases h15 : s 15 with
                        | false =>
                          exact color_witness_121 s h5 h12 h15
                        | true =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_198 s h5 h10 h12
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_50 s h5 h7 h18
                            | true =>
                              cases h3 : s 3 with
                              | false =>
                                exact color_witness_216 s h3 h5 h12
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_99 s h0 h12 h16
                                | true =>
                                  exact core_witness_10 s h1 h2 h3 h8 h9 h10 h14 h15 h16 h17 h18
                  | true =>
                    cases h8 : s 8 with
                    | false =>
                      exact color_witness_212 s h0 h8 h12
                    | true =>
                      cases h17 : s 17 with
                      | false =>
                        exact color_witness_84 s h0 h7 h17
                      | true =>
                        cases h15 : s 15 with
                        | false =>
                          exact color_witness_124 s h0 h12 h15
                        | true =>
                          cases h16 : s 16 with
                          | false =>
                            exact color_witness_99 s h0 h12 h16
                          | true =>
                            cases h10 : s 10 with
                            | false =>
                              exact color_witness_202 s h0 h10 h12
                            | true =>
                              cases h18 : s 18 with
                              | false =>
                                exact color_witness_54 s h0 h7 h18
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_213 s h0 h3 h6 h12
                                  | true =>
                                    exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
                                | true =>
                                  exact core_witness_10 s h1 h2 h3 h8 h9 h10 h14 h15 h16 h17 h18
        | true =>
          cases h1 : s 1 with
          | false =>
            cases h5 : s 5 with
            | false =>
              exact color_witness_218 s h1 h5 h12
            | true =>
              cases h2 : s 2 with
              | false =>
                cases h4 : s 4 with
                | false =>
                  exact color_witness_220 s h2 h4 h12
                | true =>
                  cases h14 : s 14 with
                  | false =>
                    exact color_witness_154 s h1 h2 h12 h14
                  | true =>
                    cases h8 : s 8 with
                    | false =>
                      exact color_witness_210 s h2 h8 h12
                    | true =>
                      cases h17 : s 17 with
                      | false =>
                        exact color_witness_82 s h2 h7 h17
                      | true =>
                        cases h6 : s 6 with
                        | false =>
                          exact color_witness_214 s h2 h6 h12
                        | true =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_200 s h2 h10 h12
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_52 s h2 h7 h18
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_123 s h2 h12 h15
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_98 s h1 h12 h16
                                | true =>
                                  exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
              | true =>
                cases h4 : s 4 with
                | false =>
                  cases h14 : s 14 with
                  | false =>
                    cases h8 : s 8 with
                    | false =>
                      exact color_witness_150 s h8 h12 h14
                    | true =>
                      cases h17 : s 17 with
                      | false =>
                        exact color_witness_59 s h7 h14 h17
                      | true =>
                        cases h10 : s 10 with
                        | false =>
                          exact color_witness_148 s h10 h12 h14
                        | true =>
                          cases h18 : s 18 with
                          | false =>
                            exact color_witness_29 s h7 h14 h18
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_153 s h3 h12 h14
                            | true =>
                              cases h6 : s 6 with
                              | false =>
                                exact color_witness_151 s h6 h12 h14
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_96 s h4 h12 h16
                                | true =>
                                  exact core_witness_7 s h0 h2 h3 h5 h6 h8 h9 h10 h16 h17 h18
                  | true =>
                    cases h8 : s 8 with
                    | false =>
                      exact color_witness_209 s h4 h8 h12
                    | true =>
                      cases h17 : s 17 with
                      | false =>
                        exact color_witness_81 s h4 h7 h17
                      | true =>
                        cases h16 : s 16 with
                        | false =>
                          exact color_witness_96 s h4 h12 h16
                        | true =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_199 s h4 h10 h12
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_51 s h4 h7 h18
                            | true =>
                              cases h3 : s 3 with
                              | false =>
                                exact color_witness_219 s h3 h4 h12
                              | true =>
                                cases h6 : s 6 with
                                | false =>
                                  exact color_witness_215 s h1 h6 h12
                                | true =>
                                  exact core_witness_7 s h0 h2 h3 h5 h6 h8 h9 h10 h16 h17 h18
                | true =>
                  cases h14 : s 14 with
                  | false =>
                    cases h8 : s 8 with
                    | false =>
                      exact color_witness_150 s h8 h12 h14
                    | true =>
                      cases h17 : s 17 with
                      | false =>
                        exact color_witness_59 s h7 h14 h17
                      | true =>
                        cases h6 : s 6 with
                        | false =>
                          exact color_witness_151 s h6 h12 h14
                        | true =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_148 s h10 h12 h14
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_29 s h7 h14 h18
                            | true =>
                              cases h3 : s 3 with
                              | false =>
                                exact color_witness_153 s h3 h12 h14
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_98 s h1 h12 h16
                                | true =>
                                  exact core_witness_7 s h0 h2 h3 h5 h6 h8 h9 h10 h16 h17 h18
                  | true =>
                    cases h8 : s 8 with
                    | false =>
                      exact color_witness_211 s h1 h8 h12
                    | true =>
                      cases h17 : s 17 with
                      | false =>
                        exact color_witness_83 s h1 h7 h17
                      | true =>
                        cases h6 : s 6 with
                        | false =>
                          exact color_witness_215 s h1 h6 h12
                        | true =>
                          cases h16 : s 16 with
                          | false =>
                            exact color_witness_98 s h1 h12 h16
                          | true =>
                            cases h10 : s 10 with
                            | false =>
                              exact color_witness_201 s h1 h10 h12
                            | true =>
                              cases h18 : s 18 with
                              | false =>
                                exact color_witness_53 s h1 h7 h18
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_122 s h1 h3 h12 h15
                                  | true =>
                                    exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
                                | true =>
                                  exact core_witness_7 s h0 h2 h3 h5 h6 h8 h9 h10 h16 h17 h18
          | true =>
            cases h4 : s 4 with
            | false =>
              cases h2 : s 2 with
              | false =>
                exact color_witness_220 s h2 h4 h12
              | true =>
                cases h5 : s 5 with
                | false =>
                  cases h14 : s 14 with
                  | false =>
                    exact color_witness_152 s h4 h5 h12 h14
                  | true =>
                    cases h8 : s 8 with
                    | false =>
                      exact color_witness_208 s h5 h8 h12
                    | true =>
                      cases h17 : s 17 with
                      | false =>
                        exact color_witness_80 s h5 h7 h17
                      | true =>
                        cases h3 : s 3 with
                        | false =>
                          exact color_witness_216 s h3 h5 h12
                        | true =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_198 s h5 h10 h12
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_50 s h5 h7 h18
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_121 s h5 h12 h15
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_96 s h4 h12 h16
                                | true =>
                                  exact core_witness_10 s h1 h2 h3 h8 h9 h10 h14 h15 h16 h17 h18
                | true =>
                  cases h14 : s 14 with
                  | false =>
                    cases h8 : s 8 with
                    | false =>
                      exact color_witness_150 s h8 h12 h14
                    | true =>
                      cases h17 : s 17 with
                      | false =>
                        exact color_witness_59 s h7 h14 h17
                      | true =>
                        cases h3 : s 3 with
                        | false =>
                          exact color_witness_153 s h3 h12 h14
                        | true =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_148 s h10 h12 h14
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_29 s h7 h14 h18
                            | true =>
                              cases h6 : s 6 with
                              | false =>
                                exact color_witness_151 s h6 h12 h14
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_96 s h4 h12 h16
                                | true =>
                                  exact core_witness_7 s h0 h2 h3 h5 h6 h8 h9 h10 h16 h17 h18
                  | true =>
                    cases h8 : s 8 with
                    | false =>
                      exact color_witness_209 s h4 h8 h12
                    | true =>
                      cases h17 : s 17 with
                      | false =>
                        exact color_witness_81 s h4 h7 h17
                      | true =>
                        cases h3 : s 3 with
                        | false =>
                          exact color_witness_219 s h3 h4 h12
                        | true =>
                          cases h16 : s 16 with
                          | false =>
                            exact color_witness_96 s h4 h12 h16
                          | true =>
                            cases h10 : s 10 with
                            | false =>
                              exact color_witness_199 s h4 h10 h12
                            | true =>
                              cases h18 : s 18 with
                              | false =>
                                exact color_witness_51 s h4 h7 h18
                              | true =>
                                cases h6 : s 6 with
                                | false =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_120 s h4 h6 h12 h15
                                  | true =>
                                    exact core_witness_10 s h1 h2 h3 h8 h9 h10 h14 h15 h16 h17 h18
                                | true =>
                                  exact core_witness_7 s h0 h2 h3 h5 h6 h8 h9 h10 h16 h17 h18
            | true =>
              cases h2 : s 2 with
              | false =>
                cases h5 : s 5 with
                | false =>
                  cases h14 : s 14 with
                  | false =>
                    cases h8 : s 8 with
                    | false =>
                      exact color_witness_150 s h8 h12 h14
                    | true =>
                      cases h17 : s 17 with
                      | false =>
                        exact color_witness_59 s h7 h14 h17
                      | true =>
                        cases h10 : s 10 with
                        | false =>
                          exact color_witness_148 s h10 h12 h14
                        | true =>
                          cases h18 : s 18 with
                          | false =>
                            exact color_witness_29 s h7 h14 h18
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_153 s h3 h12 h14
                            | true =>
                              cases h6 : s 6 with
                              | false =>
                                exact color_witness_151 s h6 h12 h14
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  exact color_witness_121 s h5 h12 h15
                                | true =>
                                  exact core_witness_4 s h0 h1 h3 h4 h6 h8 h9 h10 h15 h17 h18
                  | true =>
                    cases h8 : s 8 with
                    | false =>
                      exact color_witness_208 s h5 h8 h12
                    | true =>
                      cases h17 : s 17 with
                      | false =>
                        exact color_witness_80 s h5 h7 h17
                      | true =>
                        cases h15 : s 15 with
                        | false =>
                          exact color_witness_121 s h5 h12 h15
                        | true =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_198 s h5 h10 h12
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_50 s h5 h7 h18
                            | true =>
                              cases h3 : s 3 with
                              | false =>
                                exact color_witness_216 s h3 h5 h12
                              | true =>
                                cases h6 : s 6 with
                                | false =>
                                  exact color_witness_214 s h2 h6 h12
                                | true =>
                                  exact core_witness_4 s h0 h1 h3 h4 h6 h8 h9 h10 h15 h17 h18
                | true =>
                  cases h14 : s 14 with
                  | false =>
                    cases h8 : s 8 with
                    | false =>
                      exact color_witness_150 s h8 h12 h14
                    | true =>
                      cases h17 : s 17 with
                      | false =>
                        exact color_witness_59 s h7 h14 h17
                      | true =>
                        cases h6 : s 6 with
                        | false =>
                          exact color_witness_151 s h6 h12 h14
                        | true =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_148 s h10 h12 h14
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_29 s h7 h14 h18
                            | true =>
                              cases h3 : s 3 with
                              | false =>
                                exact color_witness_153 s h3 h12 h14
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  exact color_witness_123 s h2 h12 h15
                                | true =>
                                  exact core_witness_4 s h0 h1 h3 h4 h6 h8 h9 h10 h15 h17 h18
                  | true =>
                    cases h8 : s 8 with
                    | false =>
                      exact color_witness_210 s h2 h8 h12
                    | true =>
                      cases h17 : s 17 with
                      | false =>
                        exact color_witness_82 s h2 h7 h17
                      | true =>
                        cases h6 : s 6 with
                        | false =>
                          exact color_witness_214 s h2 h6 h12
                        | true =>
                          cases h15 : s 15 with
                          | false =>
                            exact color_witness_123 s h2 h12 h15
                          | true =>
                            cases h10 : s 10 with
                            | false =>
                              exact color_witness_200 s h2 h10 h12
                            | true =>
                              cases h18 : s 18 with
                              | false =>
                                exact color_witness_52 s h2 h7 h18
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  cases h16 : s 16 with
                                  | false =>
                                    exact color_witness_97 s h2 h3 h12 h16
                                  | true =>
                                    exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
                                | true =>
                                  exact core_witness_4 s h0 h1 h3 h4 h6 h8 h9 h10 h15 h17 h18
              | true =>
                cases h5 : s 5 with
                | false =>
                  cases h14 : s 14 with
                  | false =>
                    cases h8 : s 8 with
                    | false =>
                      exact color_witness_150 s h8 h12 h14
                    | true =>
                      cases h17 : s 17 with
                      | false =>
                        exact color_witness_59 s h7 h14 h17
                      | true =>
                        cases h3 : s 3 with
                        | false =>
                          exact color_witness_153 s h3 h12 h14
                        | true =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_148 s h10 h12 h14
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_29 s h7 h14 h18
                            | true =>
                              cases h6 : s 6 with
                              | false =>
                                exact color_witness_151 s h6 h12 h14
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  exact color_witness_121 s h5 h12 h15
                                | true =>
                                  exact core_witness_4 s h0 h1 h3 h4 h6 h8 h9 h10 h15 h17 h18
                  | true =>
                    cases h8 : s 8 with
                    | false =>
                      exact color_witness_208 s h5 h8 h12
                    | true =>
                      cases h17 : s 17 with
                      | false =>
                        exact color_witness_80 s h5 h7 h17
                      | true =>
                        cases h3 : s 3 with
                        | false =>
                          exact color_witness_216 s h3 h5 h12
                        | true =>
                          cases h15 : s 15 with
                          | false =>
                            exact color_witness_121 s h5 h12 h15
                          | true =>
                            cases h10 : s 10 with
                            | false =>
                              exact color_witness_198 s h5 h10 h12
                            | true =>
                              cases h18 : s 18 with
                              | false =>
                                exact color_witness_50 s h5 h7 h18
                              | true =>
                                cases h6 : s 6 with
                                | false =>
                                  cases h16 : s 16 with
                                  | false =>
                                    exact color_witness_95 s h5 h6 h12 h16
                                  | true =>
                                    exact core_witness_10 s h1 h2 h3 h8 h9 h10 h14 h15 h16 h17 h18
                                | true =>
                                  exact core_witness_4 s h0 h1 h3 h4 h6 h8 h9 h10 h15 h17 h18
                | true =>
                  cases h14 : s 14 with
                  | false =>
                    cases h8 : s 8 with
                    | false =>
                      exact color_witness_150 s h8 h12 h14
                    | true =>
                      cases h17 : s 17 with
                      | false =>
                        exact color_witness_59 s h7 h14 h17
                      | true =>
                        cases h3 : s 3 with
                        | false =>
                          exact color_witness_153 s h3 h12 h14
                        | true =>
                          cases h6 : s 6 with
                          | false =>
                            exact color_witness_151 s h6 h12 h14
                          | true =>
                            cases h10 : s 10 with
                            | false =>
                              exact color_witness_148 s h10 h12 h14
                            | true =>
                              cases h18 : s 18 with
                              | false =>
                                exact color_witness_29 s h7 h14 h18
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  cases h16 : s 16 with
                                  | false =>
                                    exact color_witness_86 s h12 h14 h15 h16
                                  | true =>
                                    exact core_witness_7 s h0 h2 h3 h5 h6 h8 h9 h10 h16 h17 h18
                                | true =>
                                  exact core_witness_4 s h0 h1 h3 h4 h6 h8 h9 h10 h15 h17 h18
                  | true =>
                    exact core_witness_0 s h0 h1 h2 h4 h5 h14
      | true =>
        cases h17 : s 17 with
        | false =>
          cases h18 : s 18 with
          | false =>
            cases h0 : s 0 with
            | false =>
              exact color_witness_54 s h0 h7 h18
            | true =>
              cases h1 : s 1 with
              | false =>
                exact color_witness_53 s h1 h7 h18
              | true =>
                cases h4 : s 4 with
                | false =>
                  exact color_witness_51 s h4 h7 h18
                | true =>
                  cases h2 : s 2 with
                  | false =>
                    exact color_witness_52 s h2 h7 h18
                  | true =>
                    cases h5 : s 5 with
                    | false =>
                      exact color_witness_50 s h5 h7 h18
                    | true =>
                      cases h14 : s 14 with
                      | false =>
                        exact color_witness_29 s h7 h14 h18
                      | true =>
                        exact core_witness_0 s h0 h1 h2 h4 h5 h14
          | true =>
            cases h10 : s 10 with
            | false =>
              cases h13 : s 13 with
              | false =>
                cases h0 : s 0 with
                | false =>
                  exact color_witness_64 s h0 h13 h17
                | true =>
                  cases h1 : s 1 with
                  | false =>
                    exact color_witness_63 s h1 h13 h17
                  | true =>
                    cases h4 : s 4 with
                    | false =>
                      exact color_witness_61 s h4 h13 h17
                    | true =>
                      cases h2 : s 2 with
                      | false =>
                        exact color_witness_62 s h2 h13 h17
                      | true =>
                        cases h5 : s 5 with
                        | false =>
                          exact color_witness_60 s h5 h13 h17
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            exact color_witness_55 s h13 h14 h17
                          | true =>
                            exact core_witness_0 s h0 h1 h2 h4 h5 h14
              | true =>
                cases h8 : s 8 with
                | false =>
                  cases h0 : s 0 with
                  | false =>
                    exact color_witness_74 s h0 h10 h17
                  | true =>
                    cases h1 : s 1 with
                    | false =>
                      exact color_witness_73 s h1 h10 h17
                    | true =>
                      cases h4 : s 4 with
                      | false =>
                        exact color_witness_71 s h4 h10 h17
                      | true =>
                        cases h2 : s 2 with
                        | false =>
                          exact color_witness_72 s h2 h10 h17
                        | true =>
                          cases h5 : s 5 with
                          | false =>
                            exact color_witness_70 s h5 h10 h17
                          | true =>
                            cases h14 : s 14 with
                            | false =>
                              exact color_witness_57 s h10 h14 h17
                            | true =>
                              exact core_witness_0 s h0 h1 h2 h4 h5 h14
                | true =>
                  cases h0 : s 0 with
                  | false =>
                    exact color_witness_74 s h0 h10 h17
                  | true =>
                    cases h1 : s 1 with
                    | false =>
                      exact color_witness_73 s h1 h10 h17
                    | true =>
                      cases h4 : s 4 with
                      | false =>
                        exact color_witness_71 s h4 h10 h17
                      | true =>
                        cases h2 : s 2 with
                        | false =>
                          exact color_witness_72 s h2 h10 h17
                        | true =>
                          cases h5 : s 5 with
                          | false =>
                            exact color_witness_70 s h5 h10 h17
                          | true =>
                            cases h14 : s 14 with
                            | false =>
                              exact color_witness_57 s h10 h14 h17
                            | true =>
                              exact core_witness_0 s h0 h1 h2 h4 h5 h14
            | true =>
              cases h13 : s 13 with
              | false =>
                cases h11 : s 11 with
                | false =>
                  cases h0 : s 0 with
                  | false =>
                    exact color_witness_64 s h0 h13 h17
                  | true =>
                    cases h1 : s 1 with
                    | false =>
                      exact color_witness_63 s h1 h13 h17
                    | true =>
                      cases h4 : s 4 with
                      | false =>
                        exact color_witness_61 s h4 h13 h17
                      | true =>
                        cases h2 : s 2 with
                        | false =>
                          exact color_witness_62 s h2 h13 h17
                        | true =>
                          cases h5 : s 5 with
                          | false =>
                            exact color_witness_60 s h5 h13 h17
                          | true =>
                            cases h14 : s 14 with
                            | false =>
                              exact color_witness_55 s h13 h14 h17
                            | true =>
                              exact core_witness_0 s h0 h1 h2 h4 h5 h14
                | true =>
                  cases h0 : s 0 with
                  | false =>
                    exact color_witness_64 s h0 h13 h17
                  | true =>
                    cases h1 : s 1 with
                    | false =>
                      exact color_witness_63 s h1 h13 h17
                    | true =>
                      cases h4 : s 4 with
                      | false =>
                        exact color_witness_61 s h4 h13 h17
                      | true =>
                        cases h2 : s 2 with
                        | false =>
                          exact color_witness_62 s h2 h13 h17
                        | true =>
                          cases h5 : s 5 with
                          | false =>
                            exact color_witness_60 s h5 h13 h17
                          | true =>
                            cases h14 : s 14 with
                            | false =>
                              exact color_witness_55 s h13 h14 h17
                            | true =>
                              exact core_witness_0 s h0 h1 h2 h4 h5 h14
              | true =>
                cases h0 : s 0 with
                | false =>
                  exact color_witness_84 s h0 h7 h17
                | true =>
                  cases h1 : s 1 with
                  | false =>
                    exact color_witness_83 s h1 h7 h17
                  | true =>
                    cases h4 : s 4 with
                    | false =>
                      exact color_witness_81 s h4 h7 h17
                    | true =>
                      cases h2 : s 2 with
                      | false =>
                        exact color_witness_82 s h2 h7 h17
                      | true =>
                        cases h5 : s 5 with
                        | false =>
                          exact color_witness_80 s h5 h7 h17
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            exact color_witness_59 s h7 h14 h17
                          | true =>
                            exact core_witness_0 s h0 h1 h2 h4 h5 h14
        | true =>
          cases h8 : s 8 with
          | false =>
            cases h11 : s 11 with
            | false =>
              cases h10 : s 10 with
              | false =>
                cases h13 : s 13 with
                | false =>
                  cases h0 : s 0 with
                  | false =>
                    exact color_witness_187 s h0 h7 h10 h13
                  | true =>
                    cases h1 : s 1 with
                    | false =>
                      exact color_witness_186 s h1 h7 h10 h13
                    | true =>
                      cases h4 : s 4 with
                      | false =>
                        exact color_witness_184 s h4 h7 h10 h13
                      | true =>
                        cases h2 : s 2 with
                        | false =>
                          exact color_witness_185 s h2 h7 h10 h13
                        | true =>
                          cases h5 : s 5 with
                          | false =>
                            exact color_witness_183 s h5 h7 h10 h13
                          | true =>
                            cases h14 : s 14 with
                            | false =>
                              exact color_witness_145 s h7 h10 h13 h14
                            | true =>
                              exact core_witness_0 s h0 h1 h2 h4 h5 h14
                | true =>
                  cases h18 : s 18 with
                  | false =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_39 s h0 h11 h18
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_38 s h1 h11 h18
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_36 s h4 h11 h18
                        | true =>
                          cases h2 : s 2 with
                          | false =>
                            exact color_witness_37 s h2 h11 h18
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_35 s h5 h11 h18
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_26 s h11 h14 h18
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
                  | true =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_226 s h0 h10 h11
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_225 s h1 h10 h11
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_223 s h4 h10 h11
                        | true =>
                          cases h2 : s 2 with
                          | false =>
                            exact color_witness_224 s h2 h10 h11
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_222 s h5 h10 h11
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_156 s h10 h11 h14
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
              | true =>
                cases h18 : s 18 with
                | false =>
                  cases h13 : s 13 with
                  | false =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_39 s h0 h11 h18
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_38 s h1 h11 h18
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_36 s h4 h11 h18
                        | true =>
                          cases h2 : s 2 with
                          | false =>
                            exact color_witness_37 s h2 h11 h18
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_35 s h5 h11 h18
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_26 s h11 h14 h18
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
                  | true =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_39 s h0 h11 h18
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_38 s h1 h11 h18
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_36 s h4 h11 h18
                        | true =>
                          cases h2 : s 2 with
                          | false =>
                            exact color_witness_37 s h2 h11 h18
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_35 s h5 h11 h18
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_26 s h11 h14 h18
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
                | true =>
                  cases h13 : s 13 with
                  | false =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_197 s h0 h8 h13
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_196 s h1 h8 h13
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_194 s h4 h8 h13
                        | true =>
                          cases h2 : s 2 with
                          | false =>
                            exact color_witness_195 s h2 h8 h13
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_193 s h5 h8 h13
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_147 s h8 h13 h14
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
                  | true =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_236 s h0 h7 h8 h11
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_235 s h1 h7 h8 h11
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_233 s h4 h7 h8 h11
                        | true =>
                          cases h2 : s 2 with
                          | false =>
                            exact color_witness_234 s h2 h7 h8 h11
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_232 s h5 h7 h8 h11
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_158 s h7 h8 h11 h14
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
            | true =>
              cases h10 : s 10 with
              | false =>
                cases h0 : s 0 with
                | false =>
                  cases h14 : s 14 with
                  | false =>
                    exact color_witness_163 s h0 h8 h10 h14
                  | true =>
                    cases h1 : s 1 with
                    | false =>
                      cases h4 : s 4 with
                      | false =>
                        exact color_witness_245 s h0 h1 h4 h8 h10
                      | true =>
                        cases h5 : s 5 with
                        | false =>
                          exact color_witness_242 s h1 h5 h8 h10
                        | true =>
                          cases h13 : s 13 with
                          | false =>
                            exact color_witness_186 s h1 h7 h10 h13
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_48 s h1 h8 h18
                            | true =>
                              cases h16 : s 16 with
                              | false =>
                                exact color_witness_103 s h1 h8 h10 h16
                              | true =>
                                cases h6 : s 6 with
                                | false =>
                                  exact color_witness_239 s h1 h6 h8 h10
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_129 s h0 h8 h10 h15
                                  | true =>
                                    exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
                    | true =>
                      cases h2 : s 2 with
                      | false =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_244 s h2 h4 h8 h10
                        | true =>
                          cases h5 : s 5 with
                          | false =>
                            exact color_witness_241 s h0 h2 h5 h8 h10
                          | true =>
                            cases h13 : s 13 with
                            | false =>
                              exact color_witness_185 s h2 h7 h10 h13
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_128 s h2 h8 h10 h15
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_47 s h2 h8 h18
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_238 s h2 h6 h8 h10
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_104 s h0 h8 h10 h16
                                    | true =>
                                      exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          cases h13 : s 13 with
                          | false =>
                            exact color_witness_184 s h4 h7 h10 h13
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_46 s h4 h8 h18
                            | true =>
                              cases h16 : s 16 with
                              | false =>
                                exact color_witness_101 s h4 h8 h10 h16
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  exact color_witness_243 s h3 h4 h8 h10
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_129 s h0 h8 h10 h15
                                  | true =>
                                    exact core_witness_11 s h1 h2 h3 h11 h12 h13 h14 h15 h16 h17 h18
                        | true =>
                          cases h5 : s 5 with
                          | false =>
                            cases h13 : s 13 with
                            | false =>
                              exact color_witness_183 s h5 h7 h10 h13
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_126 s h5 h8 h10 h15
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_45 s h5 h8 h18
                                | true =>
                                  cases h3 : s 3 with
                                  | false =>
                                    exact color_witness_240 s h3 h5 h8 h10
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_104 s h0 h8 h10 h16
                                    | true =>
                                      exact core_witness_11 s h1 h2 h3 h11 h12 h13 h14 h15 h16 h17 h18
                          | true =>
                            cases h13 : s 13 with
                            | false =>
                              exact color_witness_187 s h0 h7 h10 h13
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_129 s h0 h8 h10 h15
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_104 s h0 h8 h10 h16
                                | true =>
                                  cases h18 : s 18 with
                                  | false =>
                                    exact color_witness_49 s h0 h8 h18
                                  | true =>
                                    cases h3 : s 3 with
                                    | false =>
                                      cases h6 : s 6 with
                                      | false =>
                                        exact color_witness_237 s h0 h3 h6 h8 h10
                                      | true =>
                                        exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
                                    | true =>
                                      exact core_witness_11 s h1 h2 h3 h11 h12 h13 h14 h15 h16 h17 h18
                | true =>
                  cases h1 : s 1 with
                  | false =>
                    cases h5 : s 5 with
                    | false =>
                      exact color_witness_242 s h1 h5 h8 h10
                    | true =>
                      cases h2 : s 2 with
                      | false =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_244 s h2 h4 h8 h10
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            exact color_witness_162 s h1 h2 h8 h10 h14
                          | true =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_238 s h2 h6 h8 h10
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                exact color_witness_185 s h2 h7 h10 h13
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_47 s h2 h8 h18
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_128 s h2 h8 h10 h15
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_103 s h1 h8 h10 h16
                                    | true =>
                                      exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          cases h13 : s 13 with
                          | false =>
                            exact color_witness_184 s h4 h7 h10 h13
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_46 s h4 h8 h18
                            | true =>
                              cases h16 : s 16 with
                              | false =>
                                exact color_witness_101 s h4 h8 h10 h16
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  exact color_witness_243 s h3 h4 h8 h10
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_239 s h1 h6 h8 h10
                                  | true =>
                                    exact core_witness_8 s h0 h2 h3 h5 h6 h11 h12 h13 h16 h17 h18
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_159 s h6 h8 h10 h14
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                exact color_witness_145 s h7 h10 h13 h14
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_28 s h8 h14 h18
                                | true =>
                                  cases h3 : s 3 with
                                  | false =>
                                    exact color_witness_161 s h3 h8 h10 h14
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_103 s h1 h8 h10 h16
                                    | true =>
                                      exact core_witness_8 s h0 h2 h3 h5 h6 h11 h12 h13 h16 h17 h18
                          | true =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_239 s h1 h6 h8 h10
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                exact color_witness_186 s h1 h7 h10 h13
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_103 s h1 h8 h10 h16
                                | true =>
                                  cases h18 : s 18 with
                                  | false =>
                                    exact color_witness_48 s h1 h8 h18
                                  | true =>
                                    cases h3 : s 3 with
                                    | false =>
                                      cases h15 : s 15 with
                                      | false =>
                                        exact color_witness_127 s h1 h3 h8 h10 h15
                                      | true =>
                                        exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
                                    | true =>
                                      exact core_witness_8 s h0 h2 h3 h5 h6 h11 h12 h13 h16 h17 h18
                  | true =>
                    cases h4 : s 4 with
                    | false =>
                      cases h2 : s 2 with
                      | false =>
                        exact color_witness_244 s h2 h4 h8 h10
                      | true =>
                        cases h5 : s 5 with
                        | false =>
                          cases h14 : s 14 with
                          | false =>
                            exact color_witness_160 s h4 h5 h8 h10 h14
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_240 s h3 h5 h8 h10
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                exact color_witness_183 s h5 h7 h10 h13
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_45 s h5 h8 h18
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_126 s h5 h8 h10 h15
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_101 s h4 h8 h10 h16
                                    | true =>
                                      exact core_witness_11 s h1 h2 h3 h11 h12 h13 h14 h15 h16 h17 h18
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_161 s h3 h8 h10 h14
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                exact color_witness_145 s h7 h10 h13 h14
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_28 s h8 h14 h18
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_159 s h6 h8 h10 h14
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_101 s h4 h8 h10 h16
                                    | true =>
                                      exact core_witness_8 s h0 h2 h3 h5 h6 h11 h12 h13 h16 h17 h18
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_243 s h3 h4 h8 h10
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                exact color_witness_184 s h4 h7 h10 h13
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_101 s h4 h8 h10 h16
                                | true =>
                                  cases h18 : s 18 with
                                  | false =>
                                    exact color_witness_46 s h4 h8 h18
                                  | true =>
                                    cases h6 : s 6 with
                                    | false =>
                                      cases h15 : s 15 with
                                      | false =>
                                        exact color_witness_125 s h4 h6 h8 h10 h15
                                      | true =>
                                        exact core_witness_11 s h1 h2 h3 h11 h12 h13 h14 h15 h16 h17 h18
                                    | true =>
                                      exact core_witness_8 s h0 h2 h3 h5 h6 h11 h12 h13 h16 h17 h18
                    | true =>
                      cases h2 : s 2 with
                      | false =>
                        cases h5 : s 5 with
                        | false =>
                          cases h13 : s 13 with
                          | false =>
                            exact color_witness_183 s h5 h7 h10 h13
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_45 s h5 h8 h18
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_126 s h5 h8 h10 h15
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  exact color_witness_240 s h3 h5 h8 h10
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_238 s h2 h6 h8 h10
                                  | true =>
                                    exact core_witness_5 s h0 h1 h3 h4 h6 h11 h12 h13 h15 h17 h18
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_159 s h6 h8 h10 h14
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                exact color_witness_145 s h7 h10 h13 h14
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_28 s h8 h14 h18
                                | true =>
                                  cases h3 : s 3 with
                                  | false =>
                                    exact color_witness_161 s h3 h8 h10 h14
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      exact color_witness_128 s h2 h8 h10 h15
                                    | true =>
                                      exact core_witness_5 s h0 h1 h3 h4 h6 h11 h12 h13 h15 h17 h18
                          | true =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_238 s h2 h6 h8 h10
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                exact color_witness_185 s h2 h7 h10 h13
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  exact color_witness_128 s h2 h8 h10 h15
                                | true =>
                                  cases h18 : s 18 with
                                  | false =>
                                    exact color_witness_47 s h2 h8 h18
                                  | true =>
                                    cases h3 : s 3 with
                                    | false =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_102 s h2 h3 h8 h10 h16
                                      | true =>
                                        exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
                                    | true =>
                                      exact core_witness_5 s h0 h1 h3 h4 h6 h11 h12 h13 h15 h17 h18
                      | true =>
                        cases h5 : s 5 with
                        | false =>
                          cases h14 : s 14 with
                          | false =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_161 s h3 h8 h10 h14
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                exact color_witness_145 s h7 h10 h13 h14
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_28 s h8 h14 h18
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_159 s h6 h8 h10 h14
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      exact color_witness_126 s h5 h8 h10 h15
                                    | true =>
                                      exact core_witness_5 s h0 h1 h3 h4 h6 h11 h12 h13 h15 h17 h18
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_240 s h3 h5 h8 h10
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                exact color_witness_183 s h5 h7 h10 h13
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  exact color_witness_126 s h5 h8 h10 h15
                                | true =>
                                  cases h18 : s 18 with
                                  | false =>
                                    exact color_witness_45 s h5 h8 h18
                                  | true =>
                                    cases h6 : s 6 with
                                    | false =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_100 s h5 h6 h8 h10 h16
                                      | true =>
                                        exact core_witness_11 s h1 h2 h3 h11 h12 h13 h14 h15 h16 h17 h18
                                    | true =>
                                      exact core_witness_5 s h0 h1 h3 h4 h6 h11 h12 h13 h15 h17 h18
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_161 s h3 h8 h10 h14
                            | true =>
                              cases h6 : s 6 with
                              | false =>
                                exact color_witness_159 s h6 h8 h10 h14
                              | true =>
                                cases h13 : s 13 with
                                | false =>
                                  exact color_witness_145 s h7 h10 h13 h14
                                | true =>
                                  cases h18 : s 18 with
                                  | false =>
                                    exact color_witness_28 s h8 h14 h18
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_87 s h8 h10 h14 h15 h16
                                      | true =>
                                        exact core_witness_8 s h0 h2 h3 h5 h6 h11 h12 h13 h16 h17 h18
                                    | true =>
                                      exact core_witness_5 s h0 h1 h3 h4 h6 h11 h12 h13 h15 h17 h18
                          | true =>
                            exact core_witness_0 s h0 h1 h2 h4 h5 h14
              | true =>
                cases h18 : s 18 with
                | false =>
                  cases h0 : s 0 with
                  | false =>
                    exact color_witness_49 s h0 h8 h18
                  | true =>
                    cases h1 : s 1 with
                    | false =>
                      exact color_witness_48 s h1 h8 h18
                    | true =>
                      cases h4 : s 4 with
                      | false =>
                        exact color_witness_46 s h4 h8 h18
                      | true =>
                        cases h2 : s 2 with
                        | false =>
                          exact color_witness_47 s h2 h8 h18
                        | true =>
                          cases h5 : s 5 with
                          | false =>
                            exact color_witness_45 s h5 h8 h18
                          | true =>
                            cases h14 : s 14 with
                            | false =>
                              exact color_witness_28 s h8 h14 h18
                            | true =>
                              exact core_witness_0 s h0 h1 h2 h4 h5 h14
                | true =>
                  cases h13 : s 13 with
                  | false =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_197 s h0 h8 h13
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_196 s h1 h8 h13
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_194 s h4 h8 h13
                        | true =>
                          cases h2 : s 2 with
                          | false =>
                            exact color_witness_195 s h2 h8 h13
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_193 s h5 h8 h13
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_147 s h8 h13 h14
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
                  | true =>
                    cases h0 : s 0 with
                    | false =>
                      cases h14 : s 14 with
                      | false =>
                        exact color_witness_173 s h0 h7 h14
                      | true =>
                        cases h15 : s 15 with
                        | false =>
                          exact color_witness_139 s h0 h7 h15
                        | true =>
                          cases h16 : s 16 with
                          | false =>
                            exact color_witness_114 s h0 h7 h16
                          | true =>
                            cases h1 : s 1 with
                            | false =>
                              cases h4 : s 4 with
                              | false =>
                                exact color_witness_263 s h0 h1 h4 h7
                              | true =>
                                cases h5 : s 5 with
                                | false =>
                                  exact color_witness_260 s h1 h5 h7
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_257 s h1 h6 h7
                                  | true =>
                                    exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
                            | true =>
                              cases h2 : s 2 with
                              | false =>
                                cases h4 : s 4 with
                                | false =>
                                  exact color_witness_262 s h2 h4 h7
                                | true =>
                                  cases h5 : s 5 with
                                  | false =>
                                    exact color_witness_259 s h0 h2 h5 h7
                                  | true =>
                                    cases h6 : s 6 with
                                    | false =>
                                      exact color_witness_256 s h2 h6 h7
                                    | true =>
                                      exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  cases h4 : s 4 with
                                  | false =>
                                    exact color_witness_261 s h3 h4 h7
                                  | true =>
                                    cases h5 : s 5 with
                                    | false =>
                                      exact color_witness_258 s h3 h5 h7
                                    | true =>
                                      cases h6 : s 6 with
                                      | false =>
                                        exact color_witness_255 s h0 h3 h6 h7
                                      | true =>
                                        exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
                                | true =>
                                  exact core_witness_11 s h1 h2 h3 h11 h12 h13 h14 h15 h16 h17 h18
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        cases h5 : s 5 with
                        | false =>
                          exact color_witness_260 s h1 h5 h7
                        | true =>
                          cases h6 : s 6 with
                          | false =>
                            exact color_witness_257 s h1 h6 h7
                          | true =>
                            cases h16 : s 16 with
                            | false =>
                              exact color_witness_113 s h1 h7 h16
                            | true =>
                              cases h2 : s 2 with
                              | false =>
                                cases h4 : s 4 with
                                | false =>
                                  exact color_witness_262 s h2 h4 h7
                                | true =>
                                  cases h14 : s 14 with
                                  | false =>
                                    exact color_witness_172 s h1 h2 h7 h14
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      exact color_witness_138 s h2 h7 h15
                                    | true =>
                                      exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  cases h4 : s 4 with
                                  | false =>
                                    exact color_witness_261 s h3 h4 h7
                                  | true =>
                                    cases h14 : s 14 with
                                    | false =>
                                      exact color_witness_171 s h3 h7 h14
                                    | true =>
                                      cases h15 : s 15 with
                                      | false =>
                                        exact color_witness_137 s h1 h3 h7 h15
                                      | true =>
                                        exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
                                | true =>
                                  exact core_witness_8 s h0 h2 h3 h5 h6 h11 h12 h13 h16 h17 h18
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          cases h2 : s 2 with
                          | false =>
                            exact color_witness_262 s h2 h4 h7
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_261 s h3 h4 h7
                            | true =>
                              cases h16 : s 16 with
                              | false =>
                                exact color_witness_111 s h4 h7 h16
                              | true =>
                                cases h5 : s 5 with
                                | false =>
                                  cases h14 : s 14 with
                                  | false =>
                                    exact color_witness_170 s h4 h5 h7 h14
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      exact color_witness_136 s h5 h7 h15
                                    | true =>
                                      exact core_witness_11 s h1 h2 h3 h11 h12 h13 h14 h15 h16 h17 h18
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    cases h14 : s 14 with
                                    | false =>
                                      exact color_witness_169 s h6 h7 h14
                                    | true =>
                                      cases h15 : s 15 with
                                      | false =>
                                        exact color_witness_135 s h4 h6 h7 h15
                                      | true =>
                                        exact core_witness_11 s h1 h2 h3 h11 h12 h13 h14 h15 h16 h17 h18
                                  | true =>
                                    exact core_witness_8 s h0 h2 h3 h5 h6 h11 h12 h13 h16 h17 h18
                        | true =>
                          cases h2 : s 2 with
                          | false =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_256 s h2 h6 h7
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_138 s h2 h7 h15
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  cases h5 : s 5 with
                                  | false =>
                                    exact color_witness_258 s h3 h5 h7
                                  | true =>
                                    cases h14 : s 14 with
                                    | false =>
                                      exact color_witness_171 s h3 h7 h14
                                    | true =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_112 s h2 h3 h7 h16
                                      | true =>
                                        exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
                                | true =>
                                  exact core_witness_5 s h0 h1 h3 h4 h6 h11 h12 h13 h15 h17 h18
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              cases h3 : s 3 with
                              | false =>
                                exact color_witness_258 s h3 h5 h7
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  exact color_witness_136 s h5 h7 h15
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    cases h14 : s 14 with
                                    | false =>
                                      exact color_witness_169 s h6 h7 h14
                                    | true =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_110 s h5 h6 h7 h16
                                      | true =>
                                        exact core_witness_11 s h1 h2 h3 h11 h12 h13 h14 h15 h16 h17 h18
                                  | true =>
                                    exact core_witness_5 s h0 h1 h3 h4 h6 h11 h12 h13 h15 h17 h18
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                cases h3 : s 3 with
                                | false =>
                                  exact color_witness_171 s h3 h7 h14
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_169 s h6 h7 h14
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_89 s h7 h14 h15 h16
                                      | true =>
                                        exact core_witness_8 s h0 h2 h3 h5 h6 h11 h12 h13 h16 h17 h18
                                    | true =>
                                      exact core_witness_5 s h0 h1 h3 h4 h6 h11 h12 h13 h15 h17 h18
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
          | true =>
            cases h11 : s 11 with
            | false =>
              cases h13 : s 13 with
              | false =>
                cases h0 : s 0 with
                | false =>
                  cases h14 : s 14 with
                  | false =>
                    exact color_witness_144 s h0 h11 h13 h14
                  | true =>
                    cases h1 : s 1 with
                    | false =>
                      cases h4 : s 4 with
                      | false =>
                        exact color_witness_182 s h0 h1 h4 h11 h13
                      | true =>
                        cases h5 : s 5 with
                        | false =>
                          exact color_witness_179 s h1 h5 h11 h13
                        | true =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_186 s h1 h7 h10 h13
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_38 s h1 h11 h18
                            | true =>
                              cases h16 : s 16 with
                              | false =>
                                exact color_witness_93 s h1 h11 h13 h16
                              | true =>
                                cases h6 : s 6 with
                                | false =>
                                  exact color_witness_176 s h1 h6 h11 h13
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_119 s h0 h11 h13 h15
                                  | true =>
                                    exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
                    | true =>
                      cases h2 : s 2 with
                      | false =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_181 s h2 h4 h11 h13
                        | true =>
                          cases h5 : s 5 with
                          | false =>
                            exact color_witness_178 s h0 h2 h5 h11 h13
                          | true =>
                            cases h10 : s 10 with
                            | false =>
                              exact color_witness_185 s h2 h7 h10 h13
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_118 s h2 h11 h13 h15
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_37 s h2 h11 h18
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_175 s h2 h6 h11 h13
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_94 s h0 h11 h13 h16
                                    | true =>
                                      exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_184 s h4 h7 h10 h13
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_36 s h4 h11 h18
                            | true =>
                              cases h16 : s 16 with
                              | false =>
                                exact color_witness_91 s h4 h11 h13 h16
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  exact color_witness_180 s h3 h4 h11 h13
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_119 s h0 h11 h13 h15
                                  | true =>
                                    exact core_witness_10 s h1 h2 h3 h8 h9 h10 h14 h15 h16 h17 h18
                        | true =>
                          cases h5 : s 5 with
                          | false =>
                            cases h10 : s 10 with
                            | false =>
                              exact color_witness_183 s h5 h7 h10 h13
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_116 s h5 h11 h13 h15
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_35 s h5 h11 h18
                                | true =>
                                  cases h3 : s 3 with
                                  | false =>
                                    exact color_witness_177 s h3 h5 h11 h13
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_94 s h0 h11 h13 h16
                                    | true =>
                                      exact core_witness_10 s h1 h2 h3 h8 h9 h10 h14 h15 h16 h17 h18
                          | true =>
                            cases h10 : s 10 with
                            | false =>
                              exact color_witness_187 s h0 h7 h10 h13
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_119 s h0 h11 h13 h15
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_94 s h0 h11 h13 h16
                                | true =>
                                  cases h18 : s 18 with
                                  | false =>
                                    exact color_witness_39 s h0 h11 h18
                                  | true =>
                                    cases h3 : s 3 with
                                    | false =>
                                      cases h6 : s 6 with
                                      | false =>
                                        exact color_witness_174 s h0 h3 h6 h11 h13
                                      | true =>
                                        exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
                                    | true =>
                                      exact core_witness_10 s h1 h2 h3 h8 h9 h10 h14 h15 h16 h17 h18
                | true =>
                  cases h1 : s 1 with
                  | false =>
                    cases h5 : s 5 with
                    | false =>
                      exact color_witness_179 s h1 h5 h11 h13
                    | true =>
                      cases h2 : s 2 with
                      | false =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_181 s h2 h4 h11 h13
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            exact color_witness_143 s h1 h2 h11 h13 h14
                          | true =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_175 s h2 h6 h11 h13
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_185 s h2 h7 h10 h13
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_37 s h2 h11 h18
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_118 s h2 h11 h13 h15
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_93 s h1 h11 h13 h16
                                    | true =>
                                      exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_184 s h4 h7 h10 h13
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_36 s h4 h11 h18
                            | true =>
                              cases h16 : s 16 with
                              | false =>
                                exact color_witness_91 s h4 h11 h13 h16
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  exact color_witness_180 s h3 h4 h11 h13
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_176 s h1 h6 h11 h13
                                  | true =>
                                    exact core_witness_7 s h0 h2 h3 h5 h6 h8 h9 h10 h16 h17 h18
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_140 s h6 h11 h13 h14
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_145 s h7 h10 h13 h14
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_26 s h11 h14 h18
                                | true =>
                                  cases h3 : s 3 with
                                  | false =>
                                    exact color_witness_142 s h3 h11 h13 h14
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_93 s h1 h11 h13 h16
                                    | true =>
                                      exact core_witness_7 s h0 h2 h3 h5 h6 h8 h9 h10 h16 h17 h18
                          | true =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_176 s h1 h6 h11 h13
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_186 s h1 h7 h10 h13
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_93 s h1 h11 h13 h16
                                | true =>
                                  cases h18 : s 18 with
                                  | false =>
                                    exact color_witness_38 s h1 h11 h18
                                  | true =>
                                    cases h3 : s 3 with
                                    | false =>
                                      cases h15 : s 15 with
                                      | false =>
                                        exact color_witness_117 s h1 h3 h11 h13 h15
                                      | true =>
                                        exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
                                    | true =>
                                      exact core_witness_7 s h0 h2 h3 h5 h6 h8 h9 h10 h16 h17 h18
                  | true =>
                    cases h4 : s 4 with
                    | false =>
                      cases h2 : s 2 with
                      | false =>
                        exact color_witness_181 s h2 h4 h11 h13
                      | true =>
                        cases h5 : s 5 with
                        | false =>
                          cases h14 : s 14 with
                          | false =>
                            exact color_witness_141 s h4 h5 h11 h13 h14
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_177 s h3 h5 h11 h13
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_183 s h5 h7 h10 h13
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_35 s h5 h11 h18
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_116 s h5 h11 h13 h15
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_91 s h4 h11 h13 h16
                                    | true =>
                                      exact core_witness_10 s h1 h2 h3 h8 h9 h10 h14 h15 h16 h17 h18
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_142 s h3 h11 h13 h14
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_145 s h7 h10 h13 h14
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_26 s h11 h14 h18
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_140 s h6 h11 h13 h14
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_91 s h4 h11 h13 h16
                                    | true =>
                                      exact core_witness_7 s h0 h2 h3 h5 h6 h8 h9 h10 h16 h17 h18
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_180 s h3 h4 h11 h13
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_184 s h4 h7 h10 h13
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_91 s h4 h11 h13 h16
                                | true =>
                                  cases h18 : s 18 with
                                  | false =>
                                    exact color_witness_36 s h4 h11 h18
                                  | true =>
                                    cases h6 : s 6 with
                                    | false =>
                                      cases h15 : s 15 with
                                      | false =>
                                        exact color_witness_115 s h4 h6 h11 h13 h15
                                      | true =>
                                        exact core_witness_10 s h1 h2 h3 h8 h9 h10 h14 h15 h16 h17 h18
                                    | true =>
                                      exact core_witness_7 s h0 h2 h3 h5 h6 h8 h9 h10 h16 h17 h18
                    | true =>
                      cases h2 : s 2 with
                      | false =>
                        cases h5 : s 5 with
                        | false =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_183 s h5 h7 h10 h13
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_35 s h5 h11 h18
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_116 s h5 h11 h13 h15
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  exact color_witness_177 s h3 h5 h11 h13
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_175 s h2 h6 h11 h13
                                  | true =>
                                    exact core_witness_4 s h0 h1 h3 h4 h6 h8 h9 h10 h15 h17 h18
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_140 s h6 h11 h13 h14
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_145 s h7 h10 h13 h14
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_26 s h11 h14 h18
                                | true =>
                                  cases h3 : s 3 with
                                  | false =>
                                    exact color_witness_142 s h3 h11 h13 h14
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      exact color_witness_118 s h2 h11 h13 h15
                                    | true =>
                                      exact core_witness_4 s h0 h1 h3 h4 h6 h8 h9 h10 h15 h17 h18
                          | true =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_175 s h2 h6 h11 h13
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_185 s h2 h7 h10 h13
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  exact color_witness_118 s h2 h11 h13 h15
                                | true =>
                                  cases h18 : s 18 with
                                  | false =>
                                    exact color_witness_37 s h2 h11 h18
                                  | true =>
                                    cases h3 : s 3 with
                                    | false =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_92 s h2 h3 h11 h13 h16
                                      | true =>
                                        exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
                                    | true =>
                                      exact core_witness_4 s h0 h1 h3 h4 h6 h8 h9 h10 h15 h17 h18
                      | true =>
                        cases h5 : s 5 with
                        | false =>
                          cases h14 : s 14 with
                          | false =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_142 s h3 h11 h13 h14
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_145 s h7 h10 h13 h14
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_26 s h11 h14 h18
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_140 s h6 h11 h13 h14
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      exact color_witness_116 s h5 h11 h13 h15
                                    | true =>
                                      exact core_witness_4 s h0 h1 h3 h4 h6 h8 h9 h10 h15 h17 h18
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_177 s h3 h5 h11 h13
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_183 s h5 h7 h10 h13
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  exact color_witness_116 s h5 h11 h13 h15
                                | true =>
                                  cases h18 : s 18 with
                                  | false =>
                                    exact color_witness_35 s h5 h11 h18
                                  | true =>
                                    cases h6 : s 6 with
                                    | false =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_90 s h5 h6 h11 h13 h16
                                      | true =>
                                        exact core_witness_10 s h1 h2 h3 h8 h9 h10 h14 h15 h16 h17 h18
                                    | true =>
                                      exact core_witness_4 s h0 h1 h3 h4 h6 h8 h9 h10 h15 h17 h18
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_142 s h3 h11 h13 h14
                            | true =>
                              cases h6 : s 6 with
                              | false =>
                                exact color_witness_140 s h6 h11 h13 h14
                              | true =>
                                cases h10 : s 10 with
                                | false =>
                                  exact color_witness_145 s h7 h10 h13 h14
                                | true =>
                                  cases h18 : s 18 with
                                  | false =>
                                    exact color_witness_26 s h11 h14 h18
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_85 s h11 h13 h14 h15 h16
                                      | true =>
                                        exact core_witness_7 s h0 h2 h3 h5 h6 h8 h9 h10 h16 h17 h18
                                    | true =>
                                      exact core_witness_4 s h0 h1 h3 h4 h6 h8 h9 h10 h15 h17 h18
                          | true =>
                            exact core_witness_0 s h0 h1 h2 h4 h5 h14
              | true =>
                cases h18 : s 18 with
                | false =>
                  cases h0 : s 0 with
                  | false =>
                    exact color_witness_39 s h0 h11 h18
                  | true =>
                    cases h1 : s 1 with
                    | false =>
                      exact color_witness_38 s h1 h11 h18
                    | true =>
                      cases h4 : s 4 with
                      | false =>
                        exact color_witness_36 s h4 h11 h18
                      | true =>
                        cases h2 : s 2 with
                        | false =>
                          exact color_witness_37 s h2 h11 h18
                        | true =>
                          cases h5 : s 5 with
                          | false =>
                            exact color_witness_35 s h5 h11 h18
                          | true =>
                            cases h14 : s 14 with
                            | false =>
                              exact color_witness_26 s h11 h14 h18
                            | true =>
                              exact core_witness_0 s h0 h1 h2 h4 h5 h14
                | true =>
                  cases h10 : s 10 with
                  | false =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_226 s h0 h10 h11
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_225 s h1 h10 h11
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_223 s h4 h10 h11
                        | true =>
                          cases h2 : s 2 with
                          | false =>
                            exact color_witness_224 s h2 h10 h11
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_222 s h5 h10 h11
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_156 s h10 h11 h14
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
                  | true =>
                    cases h0 : s 0 with
                    | false =>
                      cases h14 : s 14 with
                      | false =>
                        exact color_witness_173 s h0 h7 h14
                      | true =>
                        cases h15 : s 15 with
                        | false =>
                          exact color_witness_139 s h0 h7 h15
                        | true =>
                          cases h16 : s 16 with
                          | false =>
                            exact color_witness_114 s h0 h7 h16
                          | true =>
                            cases h1 : s 1 with
                            | false =>
                              cases h4 : s 4 with
                              | false =>
                                exact color_witness_263 s h0 h1 h4 h7
                              | true =>
                                cases h5 : s 5 with
                                | false =>
                                  exact color_witness_260 s h1 h5 h7
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_257 s h1 h6 h7
                                  | true =>
                                    exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
                            | true =>
                              cases h2 : s 2 with
                              | false =>
                                cases h4 : s 4 with
                                | false =>
                                  exact color_witness_262 s h2 h4 h7
                                | true =>
                                  cases h5 : s 5 with
                                  | false =>
                                    exact color_witness_259 s h0 h2 h5 h7
                                  | true =>
                                    cases h6 : s 6 with
                                    | false =>
                                      exact color_witness_256 s h2 h6 h7
                                    | true =>
                                      exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  cases h4 : s 4 with
                                  | false =>
                                    exact color_witness_261 s h3 h4 h7
                                  | true =>
                                    cases h5 : s 5 with
                                    | false =>
                                      exact color_witness_258 s h3 h5 h7
                                    | true =>
                                      cases h6 : s 6 with
                                      | false =>
                                        exact color_witness_255 s h0 h3 h6 h7
                                      | true =>
                                        exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
                                | true =>
                                  exact core_witness_10 s h1 h2 h3 h8 h9 h10 h14 h15 h16 h17 h18
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        cases h5 : s 5 with
                        | false =>
                          exact color_witness_260 s h1 h5 h7
                        | true =>
                          cases h6 : s 6 with
                          | false =>
                            exact color_witness_257 s h1 h6 h7
                          | true =>
                            cases h16 : s 16 with
                            | false =>
                              exact color_witness_113 s h1 h7 h16
                            | true =>
                              cases h2 : s 2 with
                              | false =>
                                cases h4 : s 4 with
                                | false =>
                                  exact color_witness_262 s h2 h4 h7
                                | true =>
                                  cases h14 : s 14 with
                                  | false =>
                                    exact color_witness_172 s h1 h2 h7 h14
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      exact color_witness_138 s h2 h7 h15
                                    | true =>
                                      exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  cases h4 : s 4 with
                                  | false =>
                                    exact color_witness_261 s h3 h4 h7
                                  | true =>
                                    cases h14 : s 14 with
                                    | false =>
                                      exact color_witness_171 s h3 h7 h14
                                    | true =>
                                      cases h15 : s 15 with
                                      | false =>
                                        exact color_witness_137 s h1 h3 h7 h15
                                      | true =>
                                        exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
                                | true =>
                                  exact core_witness_7 s h0 h2 h3 h5 h6 h8 h9 h10 h16 h17 h18
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          cases h2 : s 2 with
                          | false =>
                            exact color_witness_262 s h2 h4 h7
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_261 s h3 h4 h7
                            | true =>
                              cases h16 : s 16 with
                              | false =>
                                exact color_witness_111 s h4 h7 h16
                              | true =>
                                cases h5 : s 5 with
                                | false =>
                                  cases h14 : s 14 with
                                  | false =>
                                    exact color_witness_170 s h4 h5 h7 h14
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      exact color_witness_136 s h5 h7 h15
                                    | true =>
                                      exact core_witness_10 s h1 h2 h3 h8 h9 h10 h14 h15 h16 h17 h18
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    cases h14 : s 14 with
                                    | false =>
                                      exact color_witness_169 s h6 h7 h14
                                    | true =>
                                      cases h15 : s 15 with
                                      | false =>
                                        exact color_witness_135 s h4 h6 h7 h15
                                      | true =>
                                        exact core_witness_10 s h1 h2 h3 h8 h9 h10 h14 h15 h16 h17 h18
                                  | true =>
                                    exact core_witness_7 s h0 h2 h3 h5 h6 h8 h9 h10 h16 h17 h18
                        | true =>
                          cases h2 : s 2 with
                          | false =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_256 s h2 h6 h7
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_138 s h2 h7 h15
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  cases h5 : s 5 with
                                  | false =>
                                    exact color_witness_258 s h3 h5 h7
                                  | true =>
                                    cases h14 : s 14 with
                                    | false =>
                                      exact color_witness_171 s h3 h7 h14
                                    | true =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_112 s h2 h3 h7 h16
                                      | true =>
                                        exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
                                | true =>
                                  exact core_witness_4 s h0 h1 h3 h4 h6 h8 h9 h10 h15 h17 h18
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              cases h3 : s 3 with
                              | false =>
                                exact color_witness_258 s h3 h5 h7
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  exact color_witness_136 s h5 h7 h15
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    cases h14 : s 14 with
                                    | false =>
                                      exact color_witness_169 s h6 h7 h14
                                    | true =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_110 s h5 h6 h7 h16
                                      | true =>
                                        exact core_witness_10 s h1 h2 h3 h8 h9 h10 h14 h15 h16 h17 h18
                                  | true =>
                                    exact core_witness_4 s h0 h1 h3 h4 h6 h8 h9 h10 h15 h17 h18
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                cases h3 : s 3 with
                                | false =>
                                  exact color_witness_171 s h3 h7 h14
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_169 s h6 h7 h14
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_89 s h7 h14 h15 h16
                                      | true =>
                                        exact core_witness_7 s h0 h2 h3 h5 h6 h8 h9 h10 h16 h17 h18
                                    | true =>
                                      exact core_witness_4 s h0 h1 h3 h4 h6 h8 h9 h10 h15 h17 h18
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
            | true =>
              cases h0 : s 0 with
              | false =>
                cases h14 : s 14 with
                | false =>
                  exact color_witness_173 s h0 h7 h14
                | true =>
                  cases h18 : s 18 with
                  | false =>
                    exact color_witness_54 s h0 h7 h18
                  | true =>
                    cases h15 : s 15 with
                    | false =>
                      exact color_witness_139 s h0 h7 h15
                    | true =>
                      cases h16 : s 16 with
                      | false =>
                        exact color_witness_114 s h0 h7 h16
                      | true =>
                        cases h1 : s 1 with
                        | false =>
                          cases h4 : s 4 with
                          | false =>
                            exact color_witness_263 s h0 h1 h4 h7
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_260 s h1 h5 h7
                            | true =>
                              cases h6 : s 6 with
                              | false =>
                                exact color_witness_257 s h1 h6 h7
                              | true =>
                                cases h10 : s 10 with
                                | false =>
                                  cases h13 : s 13 with
                                  | false =>
                                    exact color_witness_186 s h1 h7 h10 h13
                                  | true =>
                                    exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
                                | true =>
                                  exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
                        | true =>
                          cases h2 : s 2 with
                          | false =>
                            cases h4 : s 4 with
                            | false =>
                              exact color_witness_262 s h2 h4 h7
                            | true =>
                              cases h5 : s 5 with
                              | false =>
                                exact color_witness_259 s h0 h2 h5 h7
                              | true =>
                                cases h6 : s 6 with
                                | false =>
                                  exact color_witness_256 s h2 h6 h7
                                | true =>
                                  cases h10 : s 10 with
                                  | false =>
                                    cases h13 : s 13 with
                                    | false =>
                                      exact color_witness_185 s h2 h7 h10 h13
                                    | true =>
                                      exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
                                  | true =>
                                    exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              cases h4 : s 4 with
                              | false =>
                                exact color_witness_261 s h3 h4 h7
                              | true =>
                                cases h5 : s 5 with
                                | false =>
                                  exact color_witness_258 s h3 h5 h7
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_255 s h0 h3 h6 h7
                                  | true =>
                                    cases h10 : s 10 with
                                    | false =>
                                      cases h13 : s 13 with
                                      | false =>
                                        exact color_witness_187 s h0 h7 h10 h13
                                      | true =>
                                        exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
                                    | true =>
                                      exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                cases h13 : s 13 with
                                | false =>
                                  exact color_witness_187 s h0 h7 h10 h13
                                | true =>
                                  exact core_witness_11 s h1 h2 h3 h11 h12 h13 h14 h15 h16 h17 h18
                              | true =>
                                exact core_witness_10 s h1 h2 h3 h8 h9 h10 h14 h15 h16 h17 h18
              | true =>
                cases h1 : s 1 with
                | false =>
                  cases h5 : s 5 with
                  | false =>
                    exact color_witness_260 s h1 h5 h7
                  | true =>
                    cases h2 : s 2 with
                    | false =>
                      cases h4 : s 4 with
                      | false =>
                        exact color_witness_262 s h2 h4 h7
                      | true =>
                        cases h14 : s 14 with
                        | false =>
                          exact color_witness_172 s h1 h2 h7 h14
                        | true =>
                          cases h6 : s 6 with
                          | false =>
                            exact color_witness_256 s h2 h6 h7
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_52 s h2 h7 h18
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_138 s h2 h7 h15
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_113 s h1 h7 h16
                                | true =>
                                  cases h10 : s 10 with
                                  | false =>
                                    cases h13 : s 13 with
                                    | false =>
                                      exact color_witness_185 s h2 h7 h10 h13
                                    | true =>
                                      exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
                                  | true =>
                                    exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
                    | true =>
                      cases h18 : s 18 with
                      | false =>
                        exact color_witness_53 s h1 h7 h18
                      | true =>
                        cases h6 : s 6 with
                        | false =>
                          exact color_witness_257 s h1 h6 h7
                        | true =>
                          cases h16 : s 16 with
                          | false =>
                            exact color_witness_113 s h1 h7 h16
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              cases h4 : s 4 with
                              | false =>
                                exact color_witness_261 s h3 h4 h7
                              | true =>
                                cases h14 : s 14 with
                                | false =>
                                  exact color_witness_171 s h3 h7 h14
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_137 s h1 h3 h7 h15
                                  | true =>
                                    cases h10 : s 10 with
                                    | false =>
                                      cases h13 : s 13 with
                                      | false =>
                                        exact color_witness_186 s h1 h7 h10 h13
                                      | true =>
                                        exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
                                    | true =>
                                      exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                cases h13 : s 13 with
                                | false =>
                                  exact color_witness_186 s h1 h7 h10 h13
                                | true =>
                                  exact core_witness_8 s h0 h2 h3 h5 h6 h11 h12 h13 h16 h17 h18
                              | true =>
                                exact core_witness_7 s h0 h2 h3 h5 h6 h8 h9 h10 h16 h17 h18
                | true =>
                  cases h4 : s 4 with
                  | false =>
                    cases h2 : s 2 with
                    | false =>
                      exact color_witness_262 s h2 h4 h7
                    | true =>
                      cases h5 : s 5 with
                      | false =>
                        cases h14 : s 14 with
                        | false =>
                          exact color_witness_170 s h4 h5 h7 h14
                        | true =>
                          cases h3 : s 3 with
                          | false =>
                            exact color_witness_258 s h3 h5 h7
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_50 s h5 h7 h18
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_136 s h5 h7 h15
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_111 s h4 h7 h16
                                | true =>
                                  cases h10 : s 10 with
                                  | false =>
                                    cases h13 : s 13 with
                                    | false =>
                                      exact color_witness_183 s h5 h7 h10 h13
                                    | true =>
                                      exact core_witness_11 s h1 h2 h3 h11 h12 h13 h14 h15 h16 h17 h18
                                  | true =>
                                    exact core_witness_10 s h1 h2 h3 h8 h9 h10 h14 h15 h16 h17 h18
                      | true =>
                        cases h14 : s 14 with
                        | false =>
                          cases h3 : s 3 with
                          | false =>
                            exact color_witness_171 s h3 h7 h14
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_29 s h7 h14 h18
                            | true =>
                              cases h6 : s 6 with
                              | false =>
                                exact color_witness_169 s h6 h7 h14
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_111 s h4 h7 h16
                                | true =>
                                  cases h10 : s 10 with
                                  | false =>
                                    cases h13 : s 13 with
                                    | false =>
                                      exact color_witness_145 s h7 h10 h13 h14
                                    | true =>
                                      exact core_witness_8 s h0 h2 h3 h5 h6 h11 h12 h13 h16 h17 h18
                                  | true =>
                                    exact core_witness_7 s h0 h2 h3 h5 h6 h8 h9 h10 h16 h17 h18
                        | true =>
                          cases h3 : s 3 with
                          | false =>
                            exact color_witness_261 s h3 h4 h7
                          | true =>
                            cases h16 : s 16 with
                            | false =>
                              exact color_witness_111 s h4 h7 h16
                            | true =>
                              cases h18 : s 18 with
                              | false =>
                                exact color_witness_51 s h4 h7 h18
                              | true =>
                                cases h6 : s 6 with
                                | false =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_135 s h4 h6 h7 h15
                                  | true =>
                                    cases h10 : s 10 with
                                    | false =>
                                      cases h13 : s 13 with
                                      | false =>
                                        exact color_witness_184 s h4 h7 h10 h13
                                      | true =>
                                        exact core_witness_11 s h1 h2 h3 h11 h12 h13 h14 h15 h16 h17 h18
                                    | true =>
                                      exact core_witness_10 s h1 h2 h3 h8 h9 h10 h14 h15 h16 h17 h18
                                | true =>
                                  cases h10 : s 10 with
                                  | false =>
                                    cases h13 : s 13 with
                                    | false =>
                                      exact color_witness_184 s h4 h7 h10 h13
                                    | true =>
                                      exact core_witness_8 s h0 h2 h3 h5 h6 h11 h12 h13 h16 h17 h18
                                  | true =>
                                    exact core_witness_7 s h0 h2 h3 h5 h6 h8 h9 h10 h16 h17 h18
                  | true =>
                    cases h2 : s 2 with
                    | false =>
                      cases h18 : s 18 with
                      | false =>
                        exact color_witness_52 s h2 h7 h18
                      | true =>
                        cases h6 : s 6 with
                        | false =>
                          exact color_witness_256 s h2 h6 h7
                        | true =>
                          cases h15 : s 15 with
                          | false =>
                            exact color_witness_138 s h2 h7 h15
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              cases h5 : s 5 with
                              | false =>
                                exact color_witness_258 s h3 h5 h7
                              | true =>
                                cases h14 : s 14 with
                                | false =>
                                  exact color_witness_171 s h3 h7 h14
                                | true =>
                                  cases h16 : s 16 with
                                  | false =>
                                    exact color_witness_112 s h2 h3 h7 h16
                                  | true =>
                                    cases h10 : s 10 with
                                    | false =>
                                      cases h13 : s 13 with
                                      | false =>
                                        exact color_witness_185 s h2 h7 h10 h13
                                      | true =>
                                        exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
                                    | true =>
                                      exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                cases h13 : s 13 with
                                | false =>
                                  exact color_witness_185 s h2 h7 h10 h13
                                | true =>
                                  exact core_witness_5 s h0 h1 h3 h4 h6 h11 h12 h13 h15 h17 h18
                              | true =>
                                exact core_witness_4 s h0 h1 h3 h4 h6 h8 h9 h10 h15 h17 h18
                    | true =>
                      cases h5 : s 5 with
                      | false =>
                        cases h14 : s 14 with
                        | false =>
                          cases h3 : s 3 with
                          | false =>
                            exact color_witness_171 s h3 h7 h14
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_29 s h7 h14 h18
                            | true =>
                              cases h6 : s 6 with
                              | false =>
                                exact color_witness_169 s h6 h7 h14
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  exact color_witness_136 s h5 h7 h15
                                | true =>
                                  cases h10 : s 10 with
                                  | false =>
                                    cases h13 : s 13 with
                                    | false =>
                                      exact color_witness_145 s h7 h10 h13 h14
                                    | true =>
                                      exact core_witness_5 s h0 h1 h3 h4 h6 h11 h12 h13 h15 h17 h18
                                  | true =>
                                    exact core_witness_4 s h0 h1 h3 h4 h6 h8 h9 h10 h15 h17 h18
                        | true =>
                          cases h3 : s 3 with
                          | false =>
                            exact color_witness_258 s h3 h5 h7
                          | true =>
                            cases h15 : s 15 with
                            | false =>
                              exact color_witness_136 s h5 h7 h15
                            | true =>
                              cases h18 : s 18 with
                              | false =>
                                exact color_witness_50 s h5 h7 h18
                              | true =>
                                cases h6 : s 6 with
                                | false =>
                                  cases h16 : s 16 with
                                  | false =>
                                    exact color_witness_110 s h5 h6 h7 h16
                                  | true =>
                                    cases h10 : s 10 with
                                    | false =>
                                      cases h13 : s 13 with
                                      | false =>
                                        exact color_witness_183 s h5 h7 h10 h13
                                      | true =>
                                        exact core_witness_11 s h1 h2 h3 h11 h12 h13 h14 h15 h16 h17 h18
                                    | true =>
                                      exact core_witness_10 s h1 h2 h3 h8 h9 h10 h14 h15 h16 h17 h18
                                | true =>
                                  cases h10 : s 10 with
                                  | false =>
                                    cases h13 : s 13 with
                                    | false =>
                                      exact color_witness_183 s h5 h7 h10 h13
                                    | true =>
                                      exact core_witness_5 s h0 h1 h3 h4 h6 h11 h12 h13 h15 h17 h18
                                  | true =>
                                    exact core_witness_4 s h0 h1 h3 h4 h6 h8 h9 h10 h15 h17 h18
                      | true =>
                        cases h14 : s 14 with
                        | false =>
                          cases h3 : s 3 with
                          | false =>
                            exact color_witness_171 s h3 h7 h14
                          | true =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_169 s h6 h7 h14
                            | true =>
                              cases h18 : s 18 with
                              | false =>
                                exact color_witness_29 s h7 h14 h18
                              | true =>
                                cases h10 : s 10 with
                                | false =>
                                  cases h13 : s 13 with
                                  | false =>
                                    exact color_witness_145 s h7 h10 h13 h14
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_89 s h7 h14 h15 h16
                                      | true =>
                                        exact core_witness_8 s h0 h2 h3 h5 h6 h11 h12 h13 h16 h17 h18
                                    | true =>
                                      exact core_witness_5 s h0 h1 h3 h4 h6 h11 h12 h13 h15 h17 h18
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_89 s h7 h14 h15 h16
                                    | true =>
                                      exact core_witness_7 s h0 h2 h3 h5 h6 h8 h9 h10 h16 h17 h18
                                  | true =>
                                    exact core_witness_4 s h0 h1 h3 h4 h6 h8 h9 h10 h15 h17 h18
                        | true =>
                          exact core_witness_0 s h0 h1 h2 h4 h5 h14
  | true =>
    cases h9 : s 9 with
    | false =>
      cases h12 : s 12 with
      | false =>
        cases h0 : s 0 with
        | false =>
          cases h14 : s 14 with
          | false =>
            exact color_witness_155 s h0 h12 h14
          | true =>
            cases h1 : s 1 with
            | false =>
              cases h4 : s 4 with
              | false =>
                exact color_witness_221 s h0 h1 h4 h12
              | true =>
                cases h5 : s 5 with
                | false =>
                  exact color_witness_218 s h1 h5 h12
                | true =>
                  cases h2 : s 2 with
                  | false =>
                    cases h8 : s 8 with
                    | false =>
                      exact color_witness_210 s h2 h8 h12
                    | true =>
                      cases h11 : s 11 with
                      | false =>
                        exact color_witness_229 s h2 h9 h11
                      | true =>
                        cases h10 : s 10 with
                        | false =>
                          exact color_witness_200 s h2 h10 h12
                        | true =>
                          cases h13 : s 13 with
                          | false =>
                            exact color_witness_190 s h2 h9 h13
                          | true =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_214 s h2 h6 h12
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_123 s h2 h12 h15
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_98 s h1 h12 h16
                                | true =>
                                  exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
                  | true =>
                    cases h8 : s 8 with
                    | false =>
                      exact color_witness_211 s h1 h8 h12
                    | true =>
                      cases h11 : s 11 with
                      | false =>
                        exact color_witness_230 s h1 h9 h11
                      | true =>
                        cases h16 : s 16 with
                        | false =>
                          exact color_witness_98 s h1 h12 h16
                        | true =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_201 s h1 h10 h12
                          | true =>
                            cases h13 : s 13 with
                            | false =>
                              exact color_witness_191 s h1 h9 h13
                            | true =>
                              cases h6 : s 6 with
                              | false =>
                                exact color_witness_215 s h1 h6 h12
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  exact color_witness_124 s h0 h12 h15
                                | true =>
                                  exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
            | true =>
              cases h2 : s 2 with
              | false =>
                cases h4 : s 4 with
                | false =>
                  exact color_witness_220 s h2 h4 h12
                | true =>
                  cases h5 : s 5 with
                  | false =>
                    exact color_witness_217 s h0 h2 h5 h12
                  | true =>
                    cases h8 : s 8 with
                    | false =>
                      exact color_witness_210 s h2 h8 h12
                    | true =>
                      cases h11 : s 11 with
                      | false =>
                        exact color_witness_229 s h2 h9 h11
                      | true =>
                        cases h15 : s 15 with
                        | false =>
                          exact color_witness_123 s h2 h12 h15
                        | true =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_200 s h2 h10 h12
                          | true =>
                            cases h13 : s 13 with
                            | false =>
                              exact color_witness_190 s h2 h9 h13
                            | true =>
                              cases h6 : s 6 with
                              | false =>
                                exact color_witness_214 s h2 h6 h12
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_99 s h0 h12 h16
                                | true =>
                                  exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
              | true =>
                cases h4 : s 4 with
                | false =>
                  cases h5 : s 5 with
                  | false =>
                    cases h8 : s 8 with
                    | false =>
                      exact color_witness_208 s h5 h8 h12
                    | true =>
                      cases h11 : s 11 with
                      | false =>
                        exact color_witness_227 s h5 h9 h11
                      | true =>
                        cases h10 : s 10 with
                        | false =>
                          exact color_witness_198 s h5 h10 h12
                        | true =>
                          cases h13 : s 13 with
                          | false =>
                            exact color_witness_188 s h5 h9 h13
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_216 s h3 h5 h12
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_121 s h5 h12 h15
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_96 s h4 h12 h16
                                | true =>
                                  exact core_witness_9 s h1 h2 h3 h7 h8 h10 h11 h13 h14 h15 h16
                  | true =>
                    cases h8 : s 8 with
                    | false =>
                      exact color_witness_209 s h4 h8 h12
                    | true =>
                      cases h11 : s 11 with
                      | false =>
                        exact color_witness_228 s h4 h9 h11
                      | true =>
                        cases h16 : s 16 with
                        | false =>
                          exact color_witness_96 s h4 h12 h16
                        | true =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_199 s h4 h10 h12
                          | true =>
                            cases h13 : s 13 with
                            | false =>
                              exact color_witness_189 s h4 h9 h13
                            | true =>
                              cases h3 : s 3 with
                              | false =>
                                exact color_witness_219 s h3 h4 h12
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  exact color_witness_124 s h0 h12 h15
                                | true =>
                                  exact core_witness_9 s h1 h2 h3 h7 h8 h10 h11 h13 h14 h15 h16
                | true =>
                  cases h5 : s 5 with
                  | false =>
                    cases h8 : s 8 with
                    | false =>
                      exact color_witness_208 s h5 h8 h12
                    | true =>
                      cases h11 : s 11 with
                      | false =>
                        exact color_witness_227 s h5 h9 h11
                      | true =>
                        cases h15 : s 15 with
                        | false =>
                          exact color_witness_121 s h5 h12 h15
                        | true =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_198 s h5 h10 h12
                          | true =>
                            cases h13 : s 13 with
                            | false =>
                              exact color_witness_188 s h5 h9 h13
                            | true =>
                              cases h3 : s 3 with
                              | false =>
                                exact color_witness_216 s h3 h5 h12
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_99 s h0 h12 h16
                                | true =>
                                  exact core_witness_9 s h1 h2 h3 h7 h8 h10 h11 h13 h14 h15 h16
                  | true =>
                    cases h8 : s 8 with
                    | false =>
                      exact color_witness_212 s h0 h8 h12
                    | true =>
                      cases h11 : s 11 with
                      | false =>
                        exact color_witness_231 s h0 h9 h11
                      | true =>
                        cases h15 : s 15 with
                        | false =>
                          exact color_witness_124 s h0 h12 h15
                        | true =>
                          cases h16 : s 16 with
                          | false =>
                            exact color_witness_99 s h0 h12 h16
                          | true =>
                            cases h10 : s 10 with
                            | false =>
                              exact color_witness_202 s h0 h10 h12
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                exact color_witness_192 s h0 h9 h13
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_213 s h0 h3 h6 h12
                                  | true =>
                                    exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
                                | true =>
                                  exact core_witness_9 s h1 h2 h3 h7 h8 h10 h11 h13 h14 h15 h16
        | true =>
          cases h1 : s 1 with
          | false =>
            cases h5 : s 5 with
            | false =>
              exact color_witness_218 s h1 h5 h12
            | true =>
              cases h2 : s 2 with
              | false =>
                cases h4 : s 4 with
                | false =>
                  exact color_witness_220 s h2 h4 h12
                | true =>
                  cases h14 : s 14 with
                  | false =>
                    exact color_witness_154 s h1 h2 h12 h14
                  | true =>
                    cases h8 : s 8 with
                    | false =>
                      exact color_witness_210 s h2 h8 h12
                    | true =>
                      cases h11 : s 11 with
                      | false =>
                        exact color_witness_229 s h2 h9 h11
                      | true =>
                        cases h6 : s 6 with
                        | false =>
                          exact color_witness_214 s h2 h6 h12
                        | true =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_200 s h2 h10 h12
                          | true =>
                            cases h13 : s 13 with
                            | false =>
                              exact color_witness_190 s h2 h9 h13
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_123 s h2 h12 h15
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_98 s h1 h12 h16
                                | true =>
                                  exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
              | true =>
                cases h4 : s 4 with
                | false =>
                  cases h14 : s 14 with
                  | false =>
                    cases h8 : s 8 with
                    | false =>
                      exact color_witness_150 s h8 h12 h14
                    | true =>
                      cases h11 : s 11 with
                      | false =>
                        exact color_witness_157 s h9 h11 h14
                      | true =>
                        cases h10 : s 10 with
                        | false =>
                          exact color_witness_148 s h10 h12 h14
                        | true =>
                          cases h13 : s 13 with
                          | false =>
                            exact color_witness_146 s h9 h13 h14
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_153 s h3 h12 h14
                            | true =>
                              cases h6 : s 6 with
                              | false =>
                                exact color_witness_151 s h6 h12 h14
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_96 s h4 h12 h16
                                | true =>
                                  exact core_witness_6 s h0 h2 h3 h5 h6 h7 h8 h10 h11 h13 h16
                  | true =>
                    cases h8 : s 8 with
                    | false =>
                      exact color_witness_209 s h4 h8 h12
                    | true =>
                      cases h11 : s 11 with
                      | false =>
                        exact color_witness_228 s h4 h9 h11
                      | true =>
                        cases h16 : s 16 with
                        | false =>
                          exact color_witness_96 s h4 h12 h16
                        | true =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_199 s h4 h10 h12
                          | true =>
                            cases h13 : s 13 with
                            | false =>
                              exact color_witness_189 s h4 h9 h13
                            | true =>
                              cases h3 : s 3 with
                              | false =>
                                exact color_witness_219 s h3 h4 h12
                              | true =>
                                cases h6 : s 6 with
                                | false =>
                                  exact color_witness_215 s h1 h6 h12
                                | true =>
                                  exact core_witness_6 s h0 h2 h3 h5 h6 h7 h8 h10 h11 h13 h16
                | true =>
                  cases h14 : s 14 with
                  | false =>
                    cases h8 : s 8 with
                    | false =>
                      exact color_witness_150 s h8 h12 h14
                    | true =>
                      cases h11 : s 11 with
                      | false =>
                        exact color_witness_157 s h9 h11 h14
                      | true =>
                        cases h6 : s 6 with
                        | false =>
                          exact color_witness_151 s h6 h12 h14
                        | true =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_148 s h10 h12 h14
                          | true =>
                            cases h13 : s 13 with
                            | false =>
                              exact color_witness_146 s h9 h13 h14
                            | true =>
                              cases h3 : s 3 with
                              | false =>
                                exact color_witness_153 s h3 h12 h14
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_98 s h1 h12 h16
                                | true =>
                                  exact core_witness_6 s h0 h2 h3 h5 h6 h7 h8 h10 h11 h13 h16
                  | true =>
                    cases h8 : s 8 with
                    | false =>
                      exact color_witness_211 s h1 h8 h12
                    | true =>
                      cases h11 : s 11 with
                      | false =>
                        exact color_witness_230 s h1 h9 h11
                      | true =>
                        cases h6 : s 6 with
                        | false =>
                          exact color_witness_215 s h1 h6 h12
                        | true =>
                          cases h16 : s 16 with
                          | false =>
                            exact color_witness_98 s h1 h12 h16
                          | true =>
                            cases h10 : s 10 with
                            | false =>
                              exact color_witness_201 s h1 h10 h12
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                exact color_witness_191 s h1 h9 h13
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_122 s h1 h3 h12 h15
                                  | true =>
                                    exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
                                | true =>
                                  exact core_witness_6 s h0 h2 h3 h5 h6 h7 h8 h10 h11 h13 h16
          | true =>
            cases h4 : s 4 with
            | false =>
              cases h2 : s 2 with
              | false =>
                exact color_witness_220 s h2 h4 h12
              | true =>
                cases h5 : s 5 with
                | false =>
                  cases h14 : s 14 with
                  | false =>
                    exact color_witness_152 s h4 h5 h12 h14
                  | true =>
                    cases h8 : s 8 with
                    | false =>
                      exact color_witness_208 s h5 h8 h12
                    | true =>
                      cases h11 : s 11 with
                      | false =>
                        exact color_witness_227 s h5 h9 h11
                      | true =>
                        cases h3 : s 3 with
                        | false =>
                          exact color_witness_216 s h3 h5 h12
                        | true =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_198 s h5 h10 h12
                          | true =>
                            cases h13 : s 13 with
                            | false =>
                              exact color_witness_188 s h5 h9 h13
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_121 s h5 h12 h15
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_96 s h4 h12 h16
                                | true =>
                                  exact core_witness_9 s h1 h2 h3 h7 h8 h10 h11 h13 h14 h15 h16
                | true =>
                  cases h14 : s 14 with
                  | false =>
                    cases h8 : s 8 with
                    | false =>
                      exact color_witness_150 s h8 h12 h14
                    | true =>
                      cases h11 : s 11 with
                      | false =>
                        exact color_witness_157 s h9 h11 h14
                      | true =>
                        cases h3 : s 3 with
                        | false =>
                          exact color_witness_153 s h3 h12 h14
                        | true =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_148 s h10 h12 h14
                          | true =>
                            cases h13 : s 13 with
                            | false =>
                              exact color_witness_146 s h9 h13 h14
                            | true =>
                              cases h6 : s 6 with
                              | false =>
                                exact color_witness_151 s h6 h12 h14
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_96 s h4 h12 h16
                                | true =>
                                  exact core_witness_6 s h0 h2 h3 h5 h6 h7 h8 h10 h11 h13 h16
                  | true =>
                    cases h8 : s 8 with
                    | false =>
                      exact color_witness_209 s h4 h8 h12
                    | true =>
                      cases h11 : s 11 with
                      | false =>
                        exact color_witness_228 s h4 h9 h11
                      | true =>
                        cases h3 : s 3 with
                        | false =>
                          exact color_witness_219 s h3 h4 h12
                        | true =>
                          cases h16 : s 16 with
                          | false =>
                            exact color_witness_96 s h4 h12 h16
                          | true =>
                            cases h10 : s 10 with
                            | false =>
                              exact color_witness_199 s h4 h10 h12
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                exact color_witness_189 s h4 h9 h13
                              | true =>
                                cases h6 : s 6 with
                                | false =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_120 s h4 h6 h12 h15
                                  | true =>
                                    exact core_witness_9 s h1 h2 h3 h7 h8 h10 h11 h13 h14 h15 h16
                                | true =>
                                  exact core_witness_6 s h0 h2 h3 h5 h6 h7 h8 h10 h11 h13 h16
            | true =>
              cases h2 : s 2 with
              | false =>
                cases h5 : s 5 with
                | false =>
                  cases h14 : s 14 with
                  | false =>
                    cases h8 : s 8 with
                    | false =>
                      exact color_witness_150 s h8 h12 h14
                    | true =>
                      cases h11 : s 11 with
                      | false =>
                        exact color_witness_157 s h9 h11 h14
                      | true =>
                        cases h10 : s 10 with
                        | false =>
                          exact color_witness_148 s h10 h12 h14
                        | true =>
                          cases h13 : s 13 with
                          | false =>
                            exact color_witness_146 s h9 h13 h14
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_153 s h3 h12 h14
                            | true =>
                              cases h6 : s 6 with
                              | false =>
                                exact color_witness_151 s h6 h12 h14
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  exact color_witness_121 s h5 h12 h15
                                | true =>
                                  exact core_witness_3 s h0 h1 h3 h4 h6 h7 h8 h10 h11 h13 h15
                  | true =>
                    cases h8 : s 8 with
                    | false =>
                      exact color_witness_208 s h5 h8 h12
                    | true =>
                      cases h11 : s 11 with
                      | false =>
                        exact color_witness_227 s h5 h9 h11
                      | true =>
                        cases h15 : s 15 with
                        | false =>
                          exact color_witness_121 s h5 h12 h15
                        | true =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_198 s h5 h10 h12
                          | true =>
                            cases h13 : s 13 with
                            | false =>
                              exact color_witness_188 s h5 h9 h13
                            | true =>
                              cases h3 : s 3 with
                              | false =>
                                exact color_witness_216 s h3 h5 h12
                              | true =>
                                cases h6 : s 6 with
                                | false =>
                                  exact color_witness_214 s h2 h6 h12
                                | true =>
                                  exact core_witness_3 s h0 h1 h3 h4 h6 h7 h8 h10 h11 h13 h15
                | true =>
                  cases h14 : s 14 with
                  | false =>
                    cases h8 : s 8 with
                    | false =>
                      exact color_witness_150 s h8 h12 h14
                    | true =>
                      cases h11 : s 11 with
                      | false =>
                        exact color_witness_157 s h9 h11 h14
                      | true =>
                        cases h6 : s 6 with
                        | false =>
                          exact color_witness_151 s h6 h12 h14
                        | true =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_148 s h10 h12 h14
                          | true =>
                            cases h13 : s 13 with
                            | false =>
                              exact color_witness_146 s h9 h13 h14
                            | true =>
                              cases h3 : s 3 with
                              | false =>
                                exact color_witness_153 s h3 h12 h14
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  exact color_witness_123 s h2 h12 h15
                                | true =>
                                  exact core_witness_3 s h0 h1 h3 h4 h6 h7 h8 h10 h11 h13 h15
                  | true =>
                    cases h8 : s 8 with
                    | false =>
                      exact color_witness_210 s h2 h8 h12
                    | true =>
                      cases h11 : s 11 with
                      | false =>
                        exact color_witness_229 s h2 h9 h11
                      | true =>
                        cases h6 : s 6 with
                        | false =>
                          exact color_witness_214 s h2 h6 h12
                        | true =>
                          cases h15 : s 15 with
                          | false =>
                            exact color_witness_123 s h2 h12 h15
                          | true =>
                            cases h10 : s 10 with
                            | false =>
                              exact color_witness_200 s h2 h10 h12
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                exact color_witness_190 s h2 h9 h13
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  cases h16 : s 16 with
                                  | false =>
                                    exact color_witness_97 s h2 h3 h12 h16
                                  | true =>
                                    exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
                                | true =>
                                  exact core_witness_3 s h0 h1 h3 h4 h6 h7 h8 h10 h11 h13 h15
              | true =>
                cases h5 : s 5 with
                | false =>
                  cases h14 : s 14 with
                  | false =>
                    cases h8 : s 8 with
                    | false =>
                      exact color_witness_150 s h8 h12 h14
                    | true =>
                      cases h11 : s 11 with
                      | false =>
                        exact color_witness_157 s h9 h11 h14
                      | true =>
                        cases h3 : s 3 with
                        | false =>
                          exact color_witness_153 s h3 h12 h14
                        | true =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_148 s h10 h12 h14
                          | true =>
                            cases h13 : s 13 with
                            | false =>
                              exact color_witness_146 s h9 h13 h14
                            | true =>
                              cases h6 : s 6 with
                              | false =>
                                exact color_witness_151 s h6 h12 h14
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  exact color_witness_121 s h5 h12 h15
                                | true =>
                                  exact core_witness_3 s h0 h1 h3 h4 h6 h7 h8 h10 h11 h13 h15
                  | true =>
                    cases h8 : s 8 with
                    | false =>
                      exact color_witness_208 s h5 h8 h12
                    | true =>
                      cases h11 : s 11 with
                      | false =>
                        exact color_witness_227 s h5 h9 h11
                      | true =>
                        cases h3 : s 3 with
                        | false =>
                          exact color_witness_216 s h3 h5 h12
                        | true =>
                          cases h15 : s 15 with
                          | false =>
                            exact color_witness_121 s h5 h12 h15
                          | true =>
                            cases h10 : s 10 with
                            | false =>
                              exact color_witness_198 s h5 h10 h12
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                exact color_witness_188 s h5 h9 h13
                              | true =>
                                cases h6 : s 6 with
                                | false =>
                                  cases h16 : s 16 with
                                  | false =>
                                    exact color_witness_95 s h5 h6 h12 h16
                                  | true =>
                                    exact core_witness_9 s h1 h2 h3 h7 h8 h10 h11 h13 h14 h15 h16
                                | true =>
                                  exact core_witness_3 s h0 h1 h3 h4 h6 h7 h8 h10 h11 h13 h15
                | true =>
                  cases h14 : s 14 with
                  | false =>
                    cases h8 : s 8 with
                    | false =>
                      exact color_witness_150 s h8 h12 h14
                    | true =>
                      cases h11 : s 11 with
                      | false =>
                        exact color_witness_157 s h9 h11 h14
                      | true =>
                        cases h3 : s 3 with
                        | false =>
                          exact color_witness_153 s h3 h12 h14
                        | true =>
                          cases h6 : s 6 with
                          | false =>
                            exact color_witness_151 s h6 h12 h14
                          | true =>
                            cases h10 : s 10 with
                            | false =>
                              exact color_witness_148 s h10 h12 h14
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                exact color_witness_146 s h9 h13 h14
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  cases h16 : s 16 with
                                  | false =>
                                    exact color_witness_86 s h12 h14 h15 h16
                                  | true =>
                                    exact core_witness_6 s h0 h2 h3 h5 h6 h7 h8 h10 h11 h13 h16
                                | true =>
                                  exact core_witness_3 s h0 h1 h3 h4 h6 h7 h8 h10 h11 h13 h15
                  | true =>
                    exact core_witness_0 s h0 h1 h2 h4 h5 h14
      | true =>
        cases h11 : s 11 with
        | false =>
          cases h13 : s 13 with
          | false =>
            cases h0 : s 0 with
            | false =>
              exact color_witness_192 s h0 h9 h13
            | true =>
              cases h1 : s 1 with
              | false =>
                exact color_witness_191 s h1 h9 h13
              | true =>
                cases h4 : s 4 with
                | false =>
                  exact color_witness_189 s h4 h9 h13
                | true =>
                  cases h2 : s 2 with
                  | false =>
                    exact color_witness_190 s h2 h9 h13
                  | true =>
                    cases h5 : s 5 with
                    | false =>
                      exact color_witness_188 s h5 h9 h13
                    | true =>
                      cases h14 : s 14 with
                      | false =>
                        exact color_witness_146 s h9 h13 h14
                      | true =>
                        exact core_witness_0 s h0 h1 h2 h4 h5 h14
          | true =>
            cases h10 : s 10 with
            | false =>
              cases h18 : s 18 with
              | false =>
                cases h0 : s 0 with
                | false =>
                  exact color_witness_39 s h0 h11 h18
                | true =>
                  cases h1 : s 1 with
                  | false =>
                    exact color_witness_38 s h1 h11 h18
                  | true =>
                    cases h4 : s 4 with
                    | false =>
                      exact color_witness_36 s h4 h11 h18
                    | true =>
                      cases h2 : s 2 with
                      | false =>
                        exact color_witness_37 s h2 h11 h18
                      | true =>
                        cases h5 : s 5 with
                        | false =>
                          exact color_witness_35 s h5 h11 h18
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            exact color_witness_26 s h11 h14 h18
                          | true =>
                            exact core_witness_0 s h0 h1 h2 h4 h5 h14
              | true =>
                cases h8 : s 8 with
                | false =>
                  cases h0 : s 0 with
                  | false =>
                    exact color_witness_226 s h0 h10 h11
                  | true =>
                    cases h1 : s 1 with
                    | false =>
                      exact color_witness_225 s h1 h10 h11
                    | true =>
                      cases h4 : s 4 with
                      | false =>
                        exact color_witness_223 s h4 h10 h11
                      | true =>
                        cases h2 : s 2 with
                        | false =>
                          exact color_witness_224 s h2 h10 h11
                        | true =>
                          cases h5 : s 5 with
                          | false =>
                            exact color_witness_222 s h5 h10 h11
                          | true =>
                            cases h14 : s 14 with
                            | false =>
                              exact color_witness_156 s h10 h11 h14
                            | true =>
                              exact core_witness_0 s h0 h1 h2 h4 h5 h14
                | true =>
                  cases h0 : s 0 with
                  | false =>
                    exact color_witness_226 s h0 h10 h11
                  | true =>
                    cases h1 : s 1 with
                    | false =>
                      exact color_witness_225 s h1 h10 h11
                    | true =>
                      cases h4 : s 4 with
                      | false =>
                        exact color_witness_223 s h4 h10 h11
                      | true =>
                        cases h2 : s 2 with
                        | false =>
                          exact color_witness_224 s h2 h10 h11
                        | true =>
                          cases h5 : s 5 with
                          | false =>
                            exact color_witness_222 s h5 h10 h11
                          | true =>
                            cases h14 : s 14 with
                            | false =>
                              exact color_witness_156 s h10 h11 h14
                            | true =>
                              exact core_witness_0 s h0 h1 h2 h4 h5 h14
            | true =>
              cases h18 : s 18 with
              | false =>
                cases h17 : s 17 with
                | false =>
                  cases h0 : s 0 with
                  | false =>
                    exact color_witness_39 s h0 h11 h18
                  | true =>
                    cases h1 : s 1 with
                    | false =>
                      exact color_witness_38 s h1 h11 h18
                    | true =>
                      cases h4 : s 4 with
                      | false =>
                        exact color_witness_36 s h4 h11 h18
                      | true =>
                        cases h2 : s 2 with
                        | false =>
                          exact color_witness_37 s h2 h11 h18
                        | true =>
                          cases h5 : s 5 with
                          | false =>
                            exact color_witness_35 s h5 h11 h18
                          | true =>
                            cases h14 : s 14 with
                            | false =>
                              exact color_witness_26 s h11 h14 h18
                            | true =>
                              exact core_witness_0 s h0 h1 h2 h4 h5 h14
                | true =>
                  cases h0 : s 0 with
                  | false =>
                    exact color_witness_39 s h0 h11 h18
                  | true =>
                    cases h1 : s 1 with
                    | false =>
                      exact color_witness_38 s h1 h11 h18
                    | true =>
                      cases h4 : s 4 with
                      | false =>
                        exact color_witness_36 s h4 h11 h18
                      | true =>
                        cases h2 : s 2 with
                        | false =>
                          exact color_witness_37 s h2 h11 h18
                        | true =>
                          cases h5 : s 5 with
                          | false =>
                            exact color_witness_35 s h5 h11 h18
                          | true =>
                            cases h14 : s 14 with
                            | false =>
                              exact color_witness_26 s h11 h14 h18
                            | true =>
                              exact core_witness_0 s h0 h1 h2 h4 h5 h14
              | true =>
                cases h0 : s 0 with
                | false =>
                  exact color_witness_231 s h0 h9 h11
                | true =>
                  cases h1 : s 1 with
                  | false =>
                    exact color_witness_230 s h1 h9 h11
                  | true =>
                    cases h4 : s 4 with
                    | false =>
                      exact color_witness_228 s h4 h9 h11
                    | true =>
                      cases h2 : s 2 with
                      | false =>
                        exact color_witness_229 s h2 h9 h11
                      | true =>
                        cases h5 : s 5 with
                        | false =>
                          exact color_witness_227 s h5 h9 h11
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            exact color_witness_157 s h9 h11 h14
                          | true =>
                            exact core_witness_0 s h0 h1 h2 h4 h5 h14
        | true =>
          cases h8 : s 8 with
          | false =>
            cases h17 : s 17 with
            | false =>
              cases h10 : s 10 with
              | false =>
                cases h18 : s 18 with
                | false =>
                  cases h0 : s 0 with
                  | false =>
                    exact color_witness_44 s h0 h9 h10 h18
                  | true =>
                    cases h1 : s 1 with
                    | false =>
                      exact color_witness_43 s h1 h9 h10 h18
                    | true =>
                      cases h4 : s 4 with
                      | false =>
                        exact color_witness_41 s h4 h9 h10 h18
                      | true =>
                        cases h2 : s 2 with
                        | false =>
                          exact color_witness_42 s h2 h9 h10 h18
                        | true =>
                          cases h5 : s 5 with
                          | false =>
                            exact color_witness_40 s h5 h9 h10 h18
                          | true =>
                            cases h14 : s 14 with
                            | false =>
                              exact color_witness_27 s h9 h10 h14 h18
                            | true =>
                              exact core_witness_0 s h0 h1 h2 h4 h5 h14
                | true =>
                  cases h13 : s 13 with
                  | false =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_64 s h0 h13 h17
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_63 s h1 h13 h17
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_61 s h4 h13 h17
                        | true =>
                          cases h2 : s 2 with
                          | false =>
                            exact color_witness_62 s h2 h13 h17
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_60 s h5 h13 h17
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_55 s h13 h14 h17
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
                  | true =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_74 s h0 h10 h17
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_73 s h1 h10 h17
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_71 s h4 h10 h17
                        | true =>
                          cases h2 : s 2 with
                          | false =>
                            exact color_witness_72 s h2 h10 h17
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_70 s h5 h10 h17
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_57 s h10 h14 h17
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
              | true =>
                cases h13 : s 13 with
                | false =>
                  cases h18 : s 18 with
                  | false =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_49 s h0 h8 h18
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_48 s h1 h8 h18
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_46 s h4 h8 h18
                        | true =>
                          cases h2 : s 2 with
                          | false =>
                            exact color_witness_47 s h2 h8 h18
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_45 s h5 h8 h18
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_28 s h8 h14 h18
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
                  | true =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_64 s h0 h13 h17
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_63 s h1 h13 h17
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_61 s h4 h13 h17
                        | true =>
                          cases h2 : s 2 with
                          | false =>
                            exact color_witness_62 s h2 h13 h17
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_60 s h5 h13 h17
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_55 s h13 h14 h17
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
                | true =>
                  cases h18 : s 18 with
                  | false =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_49 s h0 h8 h18
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_48 s h1 h8 h18
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_46 s h4 h8 h18
                        | true =>
                          cases h2 : s 2 with
                          | false =>
                            exact color_witness_47 s h2 h8 h18
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_45 s h5 h8 h18
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_28 s h8 h14 h18
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
                  | true =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_79 s h0 h8 h9 h17
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_78 s h1 h8 h9 h17
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_76 s h4 h8 h9 h17
                        | true =>
                          cases h2 : s 2 with
                          | false =>
                            exact color_witness_77 s h2 h8 h9 h17
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_75 s h5 h8 h9 h17
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_58 s h8 h9 h14 h17
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
            | true =>
              cases h10 : s 10 with
              | false =>
                cases h0 : s 0 with
                | false =>
                  cases h14 : s 14 with
                  | false =>
                    exact color_witness_163 s h0 h8 h10 h14
                  | true =>
                    cases h1 : s 1 with
                    | false =>
                      cases h4 : s 4 with
                      | false =>
                        exact color_witness_245 s h0 h1 h4 h8 h10
                      | true =>
                        cases h5 : s 5 with
                        | false =>
                          exact color_witness_242 s h1 h5 h8 h10
                        | true =>
                          cases h13 : s 13 with
                          | false =>
                            exact color_witness_191 s h1 h9 h13
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_43 s h1 h9 h10 h18
                            | true =>
                              cases h16 : s 16 with
                              | false =>
                                exact color_witness_103 s h1 h8 h10 h16
                              | true =>
                                cases h6 : s 6 with
                                | false =>
                                  exact color_witness_239 s h1 h6 h8 h10
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_129 s h0 h8 h10 h15
                                  | true =>
                                    exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
                    | true =>
                      cases h2 : s 2 with
                      | false =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_244 s h2 h4 h8 h10
                        | true =>
                          cases h5 : s 5 with
                          | false =>
                            exact color_witness_241 s h0 h2 h5 h8 h10
                          | true =>
                            cases h13 : s 13 with
                            | false =>
                              exact color_witness_190 s h2 h9 h13
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_128 s h2 h8 h10 h15
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_42 s h2 h9 h10 h18
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_238 s h2 h6 h8 h10
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_104 s h0 h8 h10 h16
                                    | true =>
                                      exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          cases h13 : s 13 with
                          | false =>
                            exact color_witness_189 s h4 h9 h13
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_41 s h4 h9 h10 h18
                            | true =>
                              cases h16 : s 16 with
                              | false =>
                                exact color_witness_101 s h4 h8 h10 h16
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  exact color_witness_243 s h3 h4 h8 h10
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_129 s h0 h8 h10 h15
                                  | true =>
                                    exact core_witness_11 s h1 h2 h3 h11 h12 h13 h14 h15 h16 h17 h18
                        | true =>
                          cases h5 : s 5 with
                          | false =>
                            cases h13 : s 13 with
                            | false =>
                              exact color_witness_188 s h5 h9 h13
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_126 s h5 h8 h10 h15
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_40 s h5 h9 h10 h18
                                | true =>
                                  cases h3 : s 3 with
                                  | false =>
                                    exact color_witness_240 s h3 h5 h8 h10
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_104 s h0 h8 h10 h16
                                    | true =>
                                      exact core_witness_11 s h1 h2 h3 h11 h12 h13 h14 h15 h16 h17 h18
                          | true =>
                            cases h13 : s 13 with
                            | false =>
                              exact color_witness_192 s h0 h9 h13
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_129 s h0 h8 h10 h15
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_104 s h0 h8 h10 h16
                                | true =>
                                  cases h18 : s 18 with
                                  | false =>
                                    exact color_witness_44 s h0 h9 h10 h18
                                  | true =>
                                    cases h3 : s 3 with
                                    | false =>
                                      cases h6 : s 6 with
                                      | false =>
                                        exact color_witness_237 s h0 h3 h6 h8 h10
                                      | true =>
                                        exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
                                    | true =>
                                      exact core_witness_11 s h1 h2 h3 h11 h12 h13 h14 h15 h16 h17 h18
                | true =>
                  cases h1 : s 1 with
                  | false =>
                    cases h5 : s 5 with
                    | false =>
                      exact color_witness_242 s h1 h5 h8 h10
                    | true =>
                      cases h2 : s 2 with
                      | false =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_244 s h2 h4 h8 h10
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            exact color_witness_162 s h1 h2 h8 h10 h14
                          | true =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_238 s h2 h6 h8 h10
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                exact color_witness_190 s h2 h9 h13
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_42 s h2 h9 h10 h18
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_128 s h2 h8 h10 h15
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_103 s h1 h8 h10 h16
                                    | true =>
                                      exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          cases h13 : s 13 with
                          | false =>
                            exact color_witness_189 s h4 h9 h13
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_41 s h4 h9 h10 h18
                            | true =>
                              cases h16 : s 16 with
                              | false =>
                                exact color_witness_101 s h4 h8 h10 h16
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  exact color_witness_243 s h3 h4 h8 h10
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_239 s h1 h6 h8 h10
                                  | true =>
                                    exact core_witness_8 s h0 h2 h3 h5 h6 h11 h12 h13 h16 h17 h18
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_159 s h6 h8 h10 h14
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                exact color_witness_146 s h9 h13 h14
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_27 s h9 h10 h14 h18
                                | true =>
                                  cases h3 : s 3 with
                                  | false =>
                                    exact color_witness_161 s h3 h8 h10 h14
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_103 s h1 h8 h10 h16
                                    | true =>
                                      exact core_witness_8 s h0 h2 h3 h5 h6 h11 h12 h13 h16 h17 h18
                          | true =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_239 s h1 h6 h8 h10
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                exact color_witness_191 s h1 h9 h13
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_103 s h1 h8 h10 h16
                                | true =>
                                  cases h18 : s 18 with
                                  | false =>
                                    exact color_witness_43 s h1 h9 h10 h18
                                  | true =>
                                    cases h3 : s 3 with
                                    | false =>
                                      cases h15 : s 15 with
                                      | false =>
                                        exact color_witness_127 s h1 h3 h8 h10 h15
                                      | true =>
                                        exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
                                    | true =>
                                      exact core_witness_8 s h0 h2 h3 h5 h6 h11 h12 h13 h16 h17 h18
                  | true =>
                    cases h4 : s 4 with
                    | false =>
                      cases h2 : s 2 with
                      | false =>
                        exact color_witness_244 s h2 h4 h8 h10
                      | true =>
                        cases h5 : s 5 with
                        | false =>
                          cases h14 : s 14 with
                          | false =>
                            exact color_witness_160 s h4 h5 h8 h10 h14
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_240 s h3 h5 h8 h10
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                exact color_witness_188 s h5 h9 h13
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_40 s h5 h9 h10 h18
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_126 s h5 h8 h10 h15
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_101 s h4 h8 h10 h16
                                    | true =>
                                      exact core_witness_11 s h1 h2 h3 h11 h12 h13 h14 h15 h16 h17 h18
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_161 s h3 h8 h10 h14
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                exact color_witness_146 s h9 h13 h14
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_27 s h9 h10 h14 h18
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_159 s h6 h8 h10 h14
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_101 s h4 h8 h10 h16
                                    | true =>
                                      exact core_witness_8 s h0 h2 h3 h5 h6 h11 h12 h13 h16 h17 h18
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_243 s h3 h4 h8 h10
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                exact color_witness_189 s h4 h9 h13
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_101 s h4 h8 h10 h16
                                | true =>
                                  cases h18 : s 18 with
                                  | false =>
                                    exact color_witness_41 s h4 h9 h10 h18
                                  | true =>
                                    cases h6 : s 6 with
                                    | false =>
                                      cases h15 : s 15 with
                                      | false =>
                                        exact color_witness_125 s h4 h6 h8 h10 h15
                                      | true =>
                                        exact core_witness_11 s h1 h2 h3 h11 h12 h13 h14 h15 h16 h17 h18
                                    | true =>
                                      exact core_witness_8 s h0 h2 h3 h5 h6 h11 h12 h13 h16 h17 h18
                    | true =>
                      cases h2 : s 2 with
                      | false =>
                        cases h5 : s 5 with
                        | false =>
                          cases h13 : s 13 with
                          | false =>
                            exact color_witness_188 s h5 h9 h13
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_40 s h5 h9 h10 h18
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_126 s h5 h8 h10 h15
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  exact color_witness_240 s h3 h5 h8 h10
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_238 s h2 h6 h8 h10
                                  | true =>
                                    exact core_witness_5 s h0 h1 h3 h4 h6 h11 h12 h13 h15 h17 h18
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_159 s h6 h8 h10 h14
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                exact color_witness_146 s h9 h13 h14
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_27 s h9 h10 h14 h18
                                | true =>
                                  cases h3 : s 3 with
                                  | false =>
                                    exact color_witness_161 s h3 h8 h10 h14
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      exact color_witness_128 s h2 h8 h10 h15
                                    | true =>
                                      exact core_witness_5 s h0 h1 h3 h4 h6 h11 h12 h13 h15 h17 h18
                          | true =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_238 s h2 h6 h8 h10
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                exact color_witness_190 s h2 h9 h13
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  exact color_witness_128 s h2 h8 h10 h15
                                | true =>
                                  cases h18 : s 18 with
                                  | false =>
                                    exact color_witness_42 s h2 h9 h10 h18
                                  | true =>
                                    cases h3 : s 3 with
                                    | false =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_102 s h2 h3 h8 h10 h16
                                      | true =>
                                        exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
                                    | true =>
                                      exact core_witness_5 s h0 h1 h3 h4 h6 h11 h12 h13 h15 h17 h18
                      | true =>
                        cases h5 : s 5 with
                        | false =>
                          cases h14 : s 14 with
                          | false =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_161 s h3 h8 h10 h14
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                exact color_witness_146 s h9 h13 h14
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_27 s h9 h10 h14 h18
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_159 s h6 h8 h10 h14
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      exact color_witness_126 s h5 h8 h10 h15
                                    | true =>
                                      exact core_witness_5 s h0 h1 h3 h4 h6 h11 h12 h13 h15 h17 h18
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_240 s h3 h5 h8 h10
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                exact color_witness_188 s h5 h9 h13
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  exact color_witness_126 s h5 h8 h10 h15
                                | true =>
                                  cases h18 : s 18 with
                                  | false =>
                                    exact color_witness_40 s h5 h9 h10 h18
                                  | true =>
                                    cases h6 : s 6 with
                                    | false =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_100 s h5 h6 h8 h10 h16
                                      | true =>
                                        exact core_witness_11 s h1 h2 h3 h11 h12 h13 h14 h15 h16 h17 h18
                                    | true =>
                                      exact core_witness_5 s h0 h1 h3 h4 h6 h11 h12 h13 h15 h17 h18
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_161 s h3 h8 h10 h14
                            | true =>
                              cases h6 : s 6 with
                              | false =>
                                exact color_witness_159 s h6 h8 h10 h14
                              | true =>
                                cases h13 : s 13 with
                                | false =>
                                  exact color_witness_146 s h9 h13 h14
                                | true =>
                                  cases h18 : s 18 with
                                  | false =>
                                    exact color_witness_27 s h9 h10 h14 h18
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_87 s h8 h10 h14 h15 h16
                                      | true =>
                                        exact core_witness_8 s h0 h2 h3 h5 h6 h11 h12 h13 h16 h17 h18
                                    | true =>
                                      exact core_witness_5 s h0 h1 h3 h4 h6 h11 h12 h13 h15 h17 h18
                          | true =>
                            exact core_witness_0 s h0 h1 h2 h4 h5 h14
              | true =>
                cases h13 : s 13 with
                | false =>
                  cases h0 : s 0 with
                  | false =>
                    exact color_witness_192 s h0 h9 h13
                  | true =>
                    cases h1 : s 1 with
                    | false =>
                      exact color_witness_191 s h1 h9 h13
                    | true =>
                      cases h4 : s 4 with
                      | false =>
                        exact color_witness_189 s h4 h9 h13
                      | true =>
                        cases h2 : s 2 with
                        | false =>
                          exact color_witness_190 s h2 h9 h13
                        | true =>
                          cases h5 : s 5 with
                          | false =>
                            exact color_witness_188 s h5 h9 h13
                          | true =>
                            cases h14 : s 14 with
                            | false =>
                              exact color_witness_146 s h9 h13 h14
                            | true =>
                              exact core_witness_0 s h0 h1 h2 h4 h5 h14
                | true =>
                  cases h18 : s 18 with
                  | false =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_49 s h0 h8 h18
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_48 s h1 h8 h18
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_46 s h4 h8 h18
                        | true =>
                          cases h2 : s 2 with
                          | false =>
                            exact color_witness_47 s h2 h8 h18
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_45 s h5 h8 h18
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_28 s h8 h14 h18
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
                  | true =>
                    cases h0 : s 0 with
                    | false =>
                      cases h14 : s 14 with
                      | false =>
                        exact color_witness_168 s h0 h9 h14
                      | true =>
                        cases h15 : s 15 with
                        | false =>
                          exact color_witness_134 s h0 h9 h15
                        | true =>
                          cases h16 : s 16 with
                          | false =>
                            exact color_witness_109 s h0 h9 h16
                          | true =>
                            cases h1 : s 1 with
                            | false =>
                              cases h4 : s 4 with
                              | false =>
                                exact color_witness_254 s h0 h1 h4 h9
                              | true =>
                                cases h5 : s 5 with
                                | false =>
                                  exact color_witness_251 s h1 h5 h9
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_248 s h1 h6 h9
                                  | true =>
                                    exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
                            | true =>
                              cases h2 : s 2 with
                              | false =>
                                cases h4 : s 4 with
                                | false =>
                                  exact color_witness_253 s h2 h4 h9
                                | true =>
                                  cases h5 : s 5 with
                                  | false =>
                                    exact color_witness_250 s h0 h2 h5 h9
                                  | true =>
                                    cases h6 : s 6 with
                                    | false =>
                                      exact color_witness_247 s h2 h6 h9
                                    | true =>
                                      exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  cases h4 : s 4 with
                                  | false =>
                                    exact color_witness_252 s h3 h4 h9
                                  | true =>
                                    cases h5 : s 5 with
                                    | false =>
                                      exact color_witness_249 s h3 h5 h9
                                    | true =>
                                      cases h6 : s 6 with
                                      | false =>
                                        exact color_witness_246 s h0 h3 h6 h9
                                      | true =>
                                        exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
                                | true =>
                                  exact core_witness_11 s h1 h2 h3 h11 h12 h13 h14 h15 h16 h17 h18
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        cases h5 : s 5 with
                        | false =>
                          exact color_witness_251 s h1 h5 h9
                        | true =>
                          cases h6 : s 6 with
                          | false =>
                            exact color_witness_248 s h1 h6 h9
                          | true =>
                            cases h16 : s 16 with
                            | false =>
                              exact color_witness_108 s h1 h9 h16
                            | true =>
                              cases h2 : s 2 with
                              | false =>
                                cases h4 : s 4 with
                                | false =>
                                  exact color_witness_253 s h2 h4 h9
                                | true =>
                                  cases h14 : s 14 with
                                  | false =>
                                    exact color_witness_167 s h1 h2 h9 h14
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      exact color_witness_133 s h2 h9 h15
                                    | true =>
                                      exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  cases h4 : s 4 with
                                  | false =>
                                    exact color_witness_252 s h3 h4 h9
                                  | true =>
                                    cases h14 : s 14 with
                                    | false =>
                                      exact color_witness_166 s h3 h9 h14
                                    | true =>
                                      cases h15 : s 15 with
                                      | false =>
                                        exact color_witness_132 s h1 h3 h9 h15
                                      | true =>
                                        exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
                                | true =>
                                  exact core_witness_8 s h0 h2 h3 h5 h6 h11 h12 h13 h16 h17 h18
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          cases h2 : s 2 with
                          | false =>
                            exact color_witness_253 s h2 h4 h9
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_252 s h3 h4 h9
                            | true =>
                              cases h16 : s 16 with
                              | false =>
                                exact color_witness_106 s h4 h9 h16
                              | true =>
                                cases h5 : s 5 with
                                | false =>
                                  cases h14 : s 14 with
                                  | false =>
                                    exact color_witness_165 s h4 h5 h9 h14
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      exact color_witness_131 s h5 h9 h15
                                    | true =>
                                      exact core_witness_11 s h1 h2 h3 h11 h12 h13 h14 h15 h16 h17 h18
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    cases h14 : s 14 with
                                    | false =>
                                      exact color_witness_164 s h6 h9 h14
                                    | true =>
                                      cases h15 : s 15 with
                                      | false =>
                                        exact color_witness_130 s h4 h6 h9 h15
                                      | true =>
                                        exact core_witness_11 s h1 h2 h3 h11 h12 h13 h14 h15 h16 h17 h18
                                  | true =>
                                    exact core_witness_8 s h0 h2 h3 h5 h6 h11 h12 h13 h16 h17 h18
                        | true =>
                          cases h2 : s 2 with
                          | false =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_247 s h2 h6 h9
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_133 s h2 h9 h15
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  cases h5 : s 5 with
                                  | false =>
                                    exact color_witness_249 s h3 h5 h9
                                  | true =>
                                    cases h14 : s 14 with
                                    | false =>
                                      exact color_witness_166 s h3 h9 h14
                                    | true =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_107 s h2 h3 h9 h16
                                      | true =>
                                        exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
                                | true =>
                                  exact core_witness_5 s h0 h1 h3 h4 h6 h11 h12 h13 h15 h17 h18
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              cases h3 : s 3 with
                              | false =>
                                exact color_witness_249 s h3 h5 h9
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  exact color_witness_131 s h5 h9 h15
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    cases h14 : s 14 with
                                    | false =>
                                      exact color_witness_164 s h6 h9 h14
                                    | true =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_105 s h5 h6 h9 h16
                                      | true =>
                                        exact core_witness_11 s h1 h2 h3 h11 h12 h13 h14 h15 h16 h17 h18
                                  | true =>
                                    exact core_witness_5 s h0 h1 h3 h4 h6 h11 h12 h13 h15 h17 h18
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                cases h3 : s 3 with
                                | false =>
                                  exact color_witness_166 s h3 h9 h14
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_164 s h6 h9 h14
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_88 s h9 h14 h15 h16
                                      | true =>
                                        exact core_witness_8 s h0 h2 h3 h5 h6 h11 h12 h13 h16 h17 h18
                                    | true =>
                                      exact core_witness_5 s h0 h1 h3 h4 h6 h11 h12 h13 h15 h17 h18
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
          | true =>
            cases h17 : s 17 with
            | false =>
              cases h18 : s 18 with
              | false =>
                cases h0 : s 0 with
                | false =>
                  cases h14 : s 14 with
                  | false =>
                    exact color_witness_15 s h0 h14 h17 h18
                  | true =>
                    cases h1 : s 1 with
                    | false =>
                      cases h4 : s 4 with
                      | false =>
                        exact color_witness_24 s h0 h1 h4 h17 h18
                      | true =>
                        cases h5 : s 5 with
                        | false =>
                          exact color_witness_21 s h1 h5 h17 h18
                        | true =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_43 s h1 h9 h10 h18
                          | true =>
                            cases h13 : s 13 with
                            | false =>
                              exact color_witness_63 s h1 h13 h17
                            | true =>
                              cases h16 : s 16 with
                              | false =>
                                exact color_witness_4 s h1 h16 h17 h18
                              | true =>
                                cases h6 : s 6 with
                                | false =>
                                  exact color_witness_18 s h1 h6 h17 h18
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_10 s h0 h15 h17 h18
                                  | true =>
                                    exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
                    | true =>
                      cases h2 : s 2 with
                      | false =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_23 s h2 h4 h17 h18
                        | true =>
                          cases h5 : s 5 with
                          | false =>
                            exact color_witness_20 s h0 h2 h5 h17 h18
                          | true =>
                            cases h10 : s 10 with
                            | false =>
                              exact color_witness_42 s h2 h9 h10 h18
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                exact color_witness_62 s h2 h13 h17
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  exact color_witness_9 s h2 h15 h17 h18
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_17 s h2 h6 h17 h18
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_5 s h0 h16 h17 h18
                                    | true =>
                                      exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_41 s h4 h9 h10 h18
                          | true =>
                            cases h13 : s 13 with
                            | false =>
                              exact color_witness_61 s h4 h13 h17
                            | true =>
                              cases h16 : s 16 with
                              | false =>
                                exact color_witness_2 s h4 h16 h17 h18
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  exact color_witness_22 s h3 h4 h17 h18
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_10 s h0 h15 h17 h18
                                  | true =>
                                    exact core_witness_9 s h1 h2 h3 h7 h8 h10 h11 h13 h14 h15 h16
                        | true =>
                          cases h5 : s 5 with
                          | false =>
                            cases h10 : s 10 with
                            | false =>
                              exact color_witness_40 s h5 h9 h10 h18
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                exact color_witness_60 s h5 h13 h17
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  exact color_witness_7 s h5 h15 h17 h18
                                | true =>
                                  cases h3 : s 3 with
                                  | false =>
                                    exact color_witness_19 s h3 h5 h17 h18
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_5 s h0 h16 h17 h18
                                    | true =>
                                      exact core_witness_9 s h1 h2 h3 h7 h8 h10 h11 h13 h14 h15 h16
                          | true =>
                            cases h10 : s 10 with
                            | false =>
                              exact color_witness_44 s h0 h9 h10 h18
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                exact color_witness_64 s h0 h13 h17
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  exact color_witness_10 s h0 h15 h17 h18
                                | true =>
                                  cases h16 : s 16 with
                                  | false =>
                                    exact color_witness_5 s h0 h16 h17 h18
                                  | true =>
                                    cases h3 : s 3 with
                                    | false =>
                                      cases h6 : s 6 with
                                      | false =>
                                        exact color_witness_16 s h0 h3 h6 h17 h18
                                      | true =>
                                        exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
                                    | true =>
                                      exact core_witness_9 s h1 h2 h3 h7 h8 h10 h11 h13 h14 h15 h16
                | true =>
                  cases h1 : s 1 with
                  | false =>
                    cases h5 : s 5 with
                    | false =>
                      exact color_witness_21 s h1 h5 h17 h18
                    | true =>
                      cases h2 : s 2 with
                      | false =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_23 s h2 h4 h17 h18
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            exact color_witness_14 s h1 h2 h14 h17 h18
                          | true =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_17 s h2 h6 h17 h18
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_42 s h2 h9 h10 h18
                              | true =>
                                cases h13 : s 13 with
                                | false =>
                                  exact color_witness_62 s h2 h13 h17
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_9 s h2 h15 h17 h18
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_4 s h1 h16 h17 h18
                                    | true =>
                                      exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_41 s h4 h9 h10 h18
                          | true =>
                            cases h13 : s 13 with
                            | false =>
                              exact color_witness_61 s h4 h13 h17
                            | true =>
                              cases h16 : s 16 with
                              | false =>
                                exact color_witness_2 s h4 h16 h17 h18
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  exact color_witness_22 s h3 h4 h17 h18
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_18 s h1 h6 h17 h18
                                  | true =>
                                    exact core_witness_6 s h0 h2 h3 h5 h6 h7 h8 h10 h11 h13 h16
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_11 s h6 h14 h17 h18
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_27 s h9 h10 h14 h18
                              | true =>
                                cases h13 : s 13 with
                                | false =>
                                  exact color_witness_55 s h13 h14 h17
                                | true =>
                                  cases h3 : s 3 with
                                  | false =>
                                    exact color_witness_13 s h3 h14 h17 h18
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_4 s h1 h16 h17 h18
                                    | true =>
                                      exact core_witness_6 s h0 h2 h3 h5 h6 h7 h8 h10 h11 h13 h16
                          | true =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_18 s h1 h6 h17 h18
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_43 s h1 h9 h10 h18
                              | true =>
                                cases h13 : s 13 with
                                | false =>
                                  exact color_witness_63 s h1 h13 h17
                                | true =>
                                  cases h16 : s 16 with
                                  | false =>
                                    exact color_witness_4 s h1 h16 h17 h18
                                  | true =>
                                    cases h3 : s 3 with
                                    | false =>
                                      cases h15 : s 15 with
                                      | false =>
                                        exact color_witness_8 s h1 h3 h15 h17 h18
                                      | true =>
                                        exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
                                    | true =>
                                      exact core_witness_6 s h0 h2 h3 h5 h6 h7 h8 h10 h11 h13 h16
                  | true =>
                    cases h4 : s 4 with
                    | false =>
                      cases h2 : s 2 with
                      | false =>
                        exact color_witness_23 s h2 h4 h17 h18
                      | true =>
                        cases h5 : s 5 with
                        | false =>
                          cases h14 : s 14 with
                          | false =>
                            exact color_witness_12 s h4 h5 h14 h17 h18
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_19 s h3 h5 h17 h18
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_40 s h5 h9 h10 h18
                              | true =>
                                cases h13 : s 13 with
                                | false =>
                                  exact color_witness_60 s h5 h13 h17
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_7 s h5 h15 h17 h18
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_2 s h4 h16 h17 h18
                                    | true =>
                                      exact core_witness_9 s h1 h2 h3 h7 h8 h10 h11 h13 h14 h15 h16
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_13 s h3 h14 h17 h18
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_27 s h9 h10 h14 h18
                              | true =>
                                cases h13 : s 13 with
                                | false =>
                                  exact color_witness_55 s h13 h14 h17
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_11 s h6 h14 h17 h18
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_2 s h4 h16 h17 h18
                                    | true =>
                                      exact core_witness_6 s h0 h2 h3 h5 h6 h7 h8 h10 h11 h13 h16
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_22 s h3 h4 h17 h18
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_41 s h4 h9 h10 h18
                              | true =>
                                cases h13 : s 13 with
                                | false =>
                                  exact color_witness_61 s h4 h13 h17
                                | true =>
                                  cases h16 : s 16 with
                                  | false =>
                                    exact color_witness_2 s h4 h16 h17 h18
                                  | true =>
                                    cases h6 : s 6 with
                                    | false =>
                                      cases h15 : s 15 with
                                      | false =>
                                        exact color_witness_6 s h4 h6 h15 h17 h18
                                      | true =>
                                        exact core_witness_9 s h1 h2 h3 h7 h8 h10 h11 h13 h14 h15 h16
                                    | true =>
                                      exact core_witness_6 s h0 h2 h3 h5 h6 h7 h8 h10 h11 h13 h16
                    | true =>
                      cases h2 : s 2 with
                      | false =>
                        cases h5 : s 5 with
                        | false =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_40 s h5 h9 h10 h18
                          | true =>
                            cases h13 : s 13 with
                            | false =>
                              exact color_witness_60 s h5 h13 h17
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_7 s h5 h15 h17 h18
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  exact color_witness_19 s h3 h5 h17 h18
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_17 s h2 h6 h17 h18
                                  | true =>
                                    exact core_witness_3 s h0 h1 h3 h4 h6 h7 h8 h10 h11 h13 h15
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_11 s h6 h14 h17 h18
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_27 s h9 h10 h14 h18
                              | true =>
                                cases h13 : s 13 with
                                | false =>
                                  exact color_witness_55 s h13 h14 h17
                                | true =>
                                  cases h3 : s 3 with
                                  | false =>
                                    exact color_witness_13 s h3 h14 h17 h18
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      exact color_witness_9 s h2 h15 h17 h18
                                    | true =>
                                      exact core_witness_3 s h0 h1 h3 h4 h6 h7 h8 h10 h11 h13 h15
                          | true =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_17 s h2 h6 h17 h18
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_42 s h2 h9 h10 h18
                              | true =>
                                cases h13 : s 13 with
                                | false =>
                                  exact color_witness_62 s h2 h13 h17
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_9 s h2 h15 h17 h18
                                  | true =>
                                    cases h3 : s 3 with
                                    | false =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_3 s h2 h3 h16 h17 h18
                                      | true =>
                                        exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
                                    | true =>
                                      exact core_witness_3 s h0 h1 h3 h4 h6 h7 h8 h10 h11 h13 h15
                      | true =>
                        cases h5 : s 5 with
                        | false =>
                          cases h14 : s 14 with
                          | false =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_13 s h3 h14 h17 h18
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_27 s h9 h10 h14 h18
                              | true =>
                                cases h13 : s 13 with
                                | false =>
                                  exact color_witness_55 s h13 h14 h17
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_11 s h6 h14 h17 h18
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      exact color_witness_7 s h5 h15 h17 h18
                                    | true =>
                                      exact core_witness_3 s h0 h1 h3 h4 h6 h7 h8 h10 h11 h13 h15
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_19 s h3 h5 h17 h18
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_40 s h5 h9 h10 h18
                              | true =>
                                cases h13 : s 13 with
                                | false =>
                                  exact color_witness_60 s h5 h13 h17
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_7 s h5 h15 h17 h18
                                  | true =>
                                    cases h6 : s 6 with
                                    | false =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_1 s h5 h6 h16 h17 h18
                                      | true =>
                                        exact core_witness_9 s h1 h2 h3 h7 h8 h10 h11 h13 h14 h15 h16
                                    | true =>
                                      exact core_witness_3 s h0 h1 h3 h4 h6 h7 h8 h10 h11 h13 h15
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_13 s h3 h14 h17 h18
                            | true =>
                              cases h6 : s 6 with
                              | false =>
                                exact color_witness_11 s h6 h14 h17 h18
                              | true =>
                                cases h10 : s 10 with
                                | false =>
                                  exact color_witness_27 s h9 h10 h14 h18
                                | true =>
                                  cases h13 : s 13 with
                                  | false =>
                                    exact color_witness_55 s h13 h14 h17
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_0 s h14 h15 h16 h17 h18
                                      | true =>
                                        exact core_witness_6 s h0 h2 h3 h5 h6 h7 h8 h10 h11 h13 h16
                                    | true =>
                                      exact core_witness_3 s h0 h1 h3 h4 h6 h7 h8 h10 h11 h13 h15
                          | true =>
                            exact core_witness_0 s h0 h1 h2 h4 h5 h14
              | true =>
                cases h13 : s 13 with
                | false =>
                  cases h0 : s 0 with
                  | false =>
                    exact color_witness_64 s h0 h13 h17
                  | true =>
                    cases h1 : s 1 with
                    | false =>
                      exact color_witness_63 s h1 h13 h17
                    | true =>
                      cases h4 : s 4 with
                      | false =>
                        exact color_witness_61 s h4 h13 h17
                      | true =>
                        cases h2 : s 2 with
                        | false =>
                          exact color_witness_62 s h2 h13 h17
                        | true =>
                          cases h5 : s 5 with
                          | false =>
                            exact color_witness_60 s h5 h13 h17
                          | true =>
                            cases h14 : s 14 with
                            | false =>
                              exact color_witness_55 s h13 h14 h17
                            | true =>
                              exact core_witness_0 s h0 h1 h2 h4 h5 h14
                | true =>
                  cases h10 : s 10 with
                  | false =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_74 s h0 h10 h17
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_73 s h1 h10 h17
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_71 s h4 h10 h17
                        | true =>
                          cases h2 : s 2 with
                          | false =>
                            exact color_witness_72 s h2 h10 h17
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_70 s h5 h10 h17
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_57 s h10 h14 h17
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
                  | true =>
                    cases h0 : s 0 with
                    | false =>
                      cases h14 : s 14 with
                      | false =>
                        exact color_witness_168 s h0 h9 h14
                      | true =>
                        cases h15 : s 15 with
                        | false =>
                          exact color_witness_134 s h0 h9 h15
                        | true =>
                          cases h16 : s 16 with
                          | false =>
                            exact color_witness_109 s h0 h9 h16
                          | true =>
                            cases h1 : s 1 with
                            | false =>
                              cases h4 : s 4 with
                              | false =>
                                exact color_witness_254 s h0 h1 h4 h9
                              | true =>
                                cases h5 : s 5 with
                                | false =>
                                  exact color_witness_251 s h1 h5 h9
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_248 s h1 h6 h9
                                  | true =>
                                    exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
                            | true =>
                              cases h2 : s 2 with
                              | false =>
                                cases h4 : s 4 with
                                | false =>
                                  exact color_witness_253 s h2 h4 h9
                                | true =>
                                  cases h5 : s 5 with
                                  | false =>
                                    exact color_witness_250 s h0 h2 h5 h9
                                  | true =>
                                    cases h6 : s 6 with
                                    | false =>
                                      exact color_witness_247 s h2 h6 h9
                                    | true =>
                                      exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  cases h4 : s 4 with
                                  | false =>
                                    exact color_witness_252 s h3 h4 h9
                                  | true =>
                                    cases h5 : s 5 with
                                    | false =>
                                      exact color_witness_249 s h3 h5 h9
                                    | true =>
                                      cases h6 : s 6 with
                                      | false =>
                                        exact color_witness_246 s h0 h3 h6 h9
                                      | true =>
                                        exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
                                | true =>
                                  exact core_witness_9 s h1 h2 h3 h7 h8 h10 h11 h13 h14 h15 h16
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        cases h5 : s 5 with
                        | false =>
                          exact color_witness_251 s h1 h5 h9
                        | true =>
                          cases h6 : s 6 with
                          | false =>
                            exact color_witness_248 s h1 h6 h9
                          | true =>
                            cases h16 : s 16 with
                            | false =>
                              exact color_witness_108 s h1 h9 h16
                            | true =>
                              cases h2 : s 2 with
                              | false =>
                                cases h4 : s 4 with
                                | false =>
                                  exact color_witness_253 s h2 h4 h9
                                | true =>
                                  cases h14 : s 14 with
                                  | false =>
                                    exact color_witness_167 s h1 h2 h9 h14
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      exact color_witness_133 s h2 h9 h15
                                    | true =>
                                      exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  cases h4 : s 4 with
                                  | false =>
                                    exact color_witness_252 s h3 h4 h9
                                  | true =>
                                    cases h14 : s 14 with
                                    | false =>
                                      exact color_witness_166 s h3 h9 h14
                                    | true =>
                                      cases h15 : s 15 with
                                      | false =>
                                        exact color_witness_132 s h1 h3 h9 h15
                                      | true =>
                                        exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
                                | true =>
                                  exact core_witness_6 s h0 h2 h3 h5 h6 h7 h8 h10 h11 h13 h16
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          cases h2 : s 2 with
                          | false =>
                            exact color_witness_253 s h2 h4 h9
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_252 s h3 h4 h9
                            | true =>
                              cases h16 : s 16 with
                              | false =>
                                exact color_witness_106 s h4 h9 h16
                              | true =>
                                cases h5 : s 5 with
                                | false =>
                                  cases h14 : s 14 with
                                  | false =>
                                    exact color_witness_165 s h4 h5 h9 h14
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      exact color_witness_131 s h5 h9 h15
                                    | true =>
                                      exact core_witness_9 s h1 h2 h3 h7 h8 h10 h11 h13 h14 h15 h16
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    cases h14 : s 14 with
                                    | false =>
                                      exact color_witness_164 s h6 h9 h14
                                    | true =>
                                      cases h15 : s 15 with
                                      | false =>
                                        exact color_witness_130 s h4 h6 h9 h15
                                      | true =>
                                        exact core_witness_9 s h1 h2 h3 h7 h8 h10 h11 h13 h14 h15 h16
                                  | true =>
                                    exact core_witness_6 s h0 h2 h3 h5 h6 h7 h8 h10 h11 h13 h16
                        | true =>
                          cases h2 : s 2 with
                          | false =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_247 s h2 h6 h9
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_133 s h2 h9 h15
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  cases h5 : s 5 with
                                  | false =>
                                    exact color_witness_249 s h3 h5 h9
                                  | true =>
                                    cases h14 : s 14 with
                                    | false =>
                                      exact color_witness_166 s h3 h9 h14
                                    | true =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_107 s h2 h3 h9 h16
                                      | true =>
                                        exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
                                | true =>
                                  exact core_witness_3 s h0 h1 h3 h4 h6 h7 h8 h10 h11 h13 h15
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              cases h3 : s 3 with
                              | false =>
                                exact color_witness_249 s h3 h5 h9
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  exact color_witness_131 s h5 h9 h15
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    cases h14 : s 14 with
                                    | false =>
                                      exact color_witness_164 s h6 h9 h14
                                    | true =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_105 s h5 h6 h9 h16
                                      | true =>
                                        exact core_witness_9 s h1 h2 h3 h7 h8 h10 h11 h13 h14 h15 h16
                                  | true =>
                                    exact core_witness_3 s h0 h1 h3 h4 h6 h7 h8 h10 h11 h13 h15
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                cases h3 : s 3 with
                                | false =>
                                  exact color_witness_166 s h3 h9 h14
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_164 s h6 h9 h14
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_88 s h9 h14 h15 h16
                                      | true =>
                                        exact core_witness_6 s h0 h2 h3 h5 h6 h7 h8 h10 h11 h13 h16
                                    | true =>
                                      exact core_witness_3 s h0 h1 h3 h4 h6 h7 h8 h10 h11 h13 h15
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
            | true =>
              cases h0 : s 0 with
              | false =>
                cases h13 : s 13 with
                | false =>
                  exact color_witness_192 s h0 h9 h13
                | true =>
                  cases h14 : s 14 with
                  | false =>
                    exact color_witness_168 s h0 h9 h14
                  | true =>
                    cases h15 : s 15 with
                    | false =>
                      exact color_witness_134 s h0 h9 h15
                    | true =>
                      cases h16 : s 16 with
                      | false =>
                        exact color_witness_109 s h0 h9 h16
                      | true =>
                        cases h1 : s 1 with
                        | false =>
                          cases h4 : s 4 with
                          | false =>
                            exact color_witness_254 s h0 h1 h4 h9
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_251 s h1 h5 h9
                            | true =>
                              cases h6 : s 6 with
                              | false =>
                                exact color_witness_248 s h1 h6 h9
                              | true =>
                                cases h10 : s 10 with
                                | false =>
                                  cases h18 : s 18 with
                                  | false =>
                                    exact color_witness_43 s h1 h9 h10 h18
                                  | true =>
                                    exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
                                | true =>
                                  exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
                        | true =>
                          cases h2 : s 2 with
                          | false =>
                            cases h4 : s 4 with
                            | false =>
                              exact color_witness_253 s h2 h4 h9
                            | true =>
                              cases h5 : s 5 with
                              | false =>
                                exact color_witness_250 s h0 h2 h5 h9
                              | true =>
                                cases h6 : s 6 with
                                | false =>
                                  exact color_witness_247 s h2 h6 h9
                                | true =>
                                  cases h10 : s 10 with
                                  | false =>
                                    cases h18 : s 18 with
                                    | false =>
                                      exact color_witness_42 s h2 h9 h10 h18
                                    | true =>
                                      exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
                                  | true =>
                                    exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              cases h4 : s 4 with
                              | false =>
                                exact color_witness_252 s h3 h4 h9
                              | true =>
                                cases h5 : s 5 with
                                | false =>
                                  exact color_witness_249 s h3 h5 h9
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_246 s h0 h3 h6 h9
                                  | true =>
                                    cases h10 : s 10 with
                                    | false =>
                                      cases h18 : s 18 with
                                      | false =>
                                        exact color_witness_44 s h0 h9 h10 h18
                                      | true =>
                                        exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
                                    | true =>
                                      exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_44 s h0 h9 h10 h18
                                | true =>
                                  exact core_witness_11 s h1 h2 h3 h11 h12 h13 h14 h15 h16 h17 h18
                              | true =>
                                exact core_witness_9 s h1 h2 h3 h7 h8 h10 h11 h13 h14 h15 h16
              | true =>
                cases h1 : s 1 with
                | false =>
                  cases h5 : s 5 with
                  | false =>
                    exact color_witness_251 s h1 h5 h9
                  | true =>
                    cases h2 : s 2 with
                    | false =>
                      cases h4 : s 4 with
                      | false =>
                        exact color_witness_253 s h2 h4 h9
                      | true =>
                        cases h14 : s 14 with
                        | false =>
                          exact color_witness_167 s h1 h2 h9 h14
                        | true =>
                          cases h6 : s 6 with
                          | false =>
                            exact color_witness_247 s h2 h6 h9
                          | true =>
                            cases h13 : s 13 with
                            | false =>
                              exact color_witness_190 s h2 h9 h13
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_133 s h2 h9 h15
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_108 s h1 h9 h16
                                | true =>
                                  cases h10 : s 10 with
                                  | false =>
                                    cases h18 : s 18 with
                                    | false =>
                                      exact color_witness_42 s h2 h9 h10 h18
                                    | true =>
                                      exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
                                  | true =>
                                    exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
                    | true =>
                      cases h13 : s 13 with
                      | false =>
                        exact color_witness_191 s h1 h9 h13
                      | true =>
                        cases h6 : s 6 with
                        | false =>
                          exact color_witness_248 s h1 h6 h9
                        | true =>
                          cases h16 : s 16 with
                          | false =>
                            exact color_witness_108 s h1 h9 h16
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              cases h4 : s 4 with
                              | false =>
                                exact color_witness_252 s h3 h4 h9
                              | true =>
                                cases h14 : s 14 with
                                | false =>
                                  exact color_witness_166 s h3 h9 h14
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_132 s h1 h3 h9 h15
                                  | true =>
                                    cases h10 : s 10 with
                                    | false =>
                                      cases h18 : s 18 with
                                      | false =>
                                        exact color_witness_43 s h1 h9 h10 h18
                                      | true =>
                                        exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
                                    | true =>
                                      exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_43 s h1 h9 h10 h18
                                | true =>
                                  exact core_witness_8 s h0 h2 h3 h5 h6 h11 h12 h13 h16 h17 h18
                              | true =>
                                exact core_witness_6 s h0 h2 h3 h5 h6 h7 h8 h10 h11 h13 h16
                | true =>
                  cases h4 : s 4 with
                  | false =>
                    cases h2 : s 2 with
                    | false =>
                      exact color_witness_253 s h2 h4 h9
                    | true =>
                      cases h5 : s 5 with
                      | false =>
                        cases h14 : s 14 with
                        | false =>
                          exact color_witness_165 s h4 h5 h9 h14
                        | true =>
                          cases h3 : s 3 with
                          | false =>
                            exact color_witness_249 s h3 h5 h9
                          | true =>
                            cases h13 : s 13 with
                            | false =>
                              exact color_witness_188 s h5 h9 h13
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_131 s h5 h9 h15
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_106 s h4 h9 h16
                                | true =>
                                  cases h10 : s 10 with
                                  | false =>
                                    cases h18 : s 18 with
                                    | false =>
                                      exact color_witness_40 s h5 h9 h10 h18
                                    | true =>
                                      exact core_witness_11 s h1 h2 h3 h11 h12 h13 h14 h15 h16 h17 h18
                                  | true =>
                                    exact core_witness_9 s h1 h2 h3 h7 h8 h10 h11 h13 h14 h15 h16
                      | true =>
                        cases h14 : s 14 with
                        | false =>
                          cases h3 : s 3 with
                          | false =>
                            exact color_witness_166 s h3 h9 h14
                          | true =>
                            cases h13 : s 13 with
                            | false =>
                              exact color_witness_146 s h9 h13 h14
                            | true =>
                              cases h6 : s 6 with
                              | false =>
                                exact color_witness_164 s h6 h9 h14
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_106 s h4 h9 h16
                                | true =>
                                  cases h10 : s 10 with
                                  | false =>
                                    cases h18 : s 18 with
                                    | false =>
                                      exact color_witness_27 s h9 h10 h14 h18
                                    | true =>
                                      exact core_witness_8 s h0 h2 h3 h5 h6 h11 h12 h13 h16 h17 h18
                                  | true =>
                                    exact core_witness_6 s h0 h2 h3 h5 h6 h7 h8 h10 h11 h13 h16
                        | true =>
                          cases h3 : s 3 with
                          | false =>
                            exact color_witness_252 s h3 h4 h9
                          | true =>
                            cases h13 : s 13 with
                            | false =>
                              exact color_witness_189 s h4 h9 h13
                            | true =>
                              cases h16 : s 16 with
                              | false =>
                                exact color_witness_106 s h4 h9 h16
                              | true =>
                                cases h6 : s 6 with
                                | false =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_130 s h4 h6 h9 h15
                                  | true =>
                                    cases h10 : s 10 with
                                    | false =>
                                      cases h18 : s 18 with
                                      | false =>
                                        exact color_witness_41 s h4 h9 h10 h18
                                      | true =>
                                        exact core_witness_11 s h1 h2 h3 h11 h12 h13 h14 h15 h16 h17 h18
                                    | true =>
                                      exact core_witness_9 s h1 h2 h3 h7 h8 h10 h11 h13 h14 h15 h16
                                | true =>
                                  cases h10 : s 10 with
                                  | false =>
                                    cases h18 : s 18 with
                                    | false =>
                                      exact color_witness_41 s h4 h9 h10 h18
                                    | true =>
                                      exact core_witness_8 s h0 h2 h3 h5 h6 h11 h12 h13 h16 h17 h18
                                  | true =>
                                    exact core_witness_6 s h0 h2 h3 h5 h6 h7 h8 h10 h11 h13 h16
                  | true =>
                    cases h2 : s 2 with
                    | false =>
                      cases h13 : s 13 with
                      | false =>
                        exact color_witness_190 s h2 h9 h13
                      | true =>
                        cases h6 : s 6 with
                        | false =>
                          exact color_witness_247 s h2 h6 h9
                        | true =>
                          cases h15 : s 15 with
                          | false =>
                            exact color_witness_133 s h2 h9 h15
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              cases h5 : s 5 with
                              | false =>
                                exact color_witness_249 s h3 h5 h9
                              | true =>
                                cases h14 : s 14 with
                                | false =>
                                  exact color_witness_166 s h3 h9 h14
                                | true =>
                                  cases h16 : s 16 with
                                  | false =>
                                    exact color_witness_107 s h2 h3 h9 h16
                                  | true =>
                                    cases h10 : s 10 with
                                    | false =>
                                      cases h18 : s 18 with
                                      | false =>
                                        exact color_witness_42 s h2 h9 h10 h18
                                      | true =>
                                        exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
                                    | true =>
                                      exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_42 s h2 h9 h10 h18
                                | true =>
                                  exact core_witness_5 s h0 h1 h3 h4 h6 h11 h12 h13 h15 h17 h18
                              | true =>
                                exact core_witness_3 s h0 h1 h3 h4 h6 h7 h8 h10 h11 h13 h15
                    | true =>
                      cases h5 : s 5 with
                      | false =>
                        cases h14 : s 14 with
                        | false =>
                          cases h3 : s 3 with
                          | false =>
                            exact color_witness_166 s h3 h9 h14
                          | true =>
                            cases h13 : s 13 with
                            | false =>
                              exact color_witness_146 s h9 h13 h14
                            | true =>
                              cases h6 : s 6 with
                              | false =>
                                exact color_witness_164 s h6 h9 h14
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  exact color_witness_131 s h5 h9 h15
                                | true =>
                                  cases h10 : s 10 with
                                  | false =>
                                    cases h18 : s 18 with
                                    | false =>
                                      exact color_witness_27 s h9 h10 h14 h18
                                    | true =>
                                      exact core_witness_5 s h0 h1 h3 h4 h6 h11 h12 h13 h15 h17 h18
                                  | true =>
                                    exact core_witness_3 s h0 h1 h3 h4 h6 h7 h8 h10 h11 h13 h15
                        | true =>
                          cases h3 : s 3 with
                          | false =>
                            exact color_witness_249 s h3 h5 h9
                          | true =>
                            cases h13 : s 13 with
                            | false =>
                              exact color_witness_188 s h5 h9 h13
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_131 s h5 h9 h15
                              | true =>
                                cases h6 : s 6 with
                                | false =>
                                  cases h16 : s 16 with
                                  | false =>
                                    exact color_witness_105 s h5 h6 h9 h16
                                  | true =>
                                    cases h10 : s 10 with
                                    | false =>
                                      cases h18 : s 18 with
                                      | false =>
                                        exact color_witness_40 s h5 h9 h10 h18
                                      | true =>
                                        exact core_witness_11 s h1 h2 h3 h11 h12 h13 h14 h15 h16 h17 h18
                                    | true =>
                                      exact core_witness_9 s h1 h2 h3 h7 h8 h10 h11 h13 h14 h15 h16
                                | true =>
                                  cases h10 : s 10 with
                                  | false =>
                                    cases h18 : s 18 with
                                    | false =>
                                      exact color_witness_40 s h5 h9 h10 h18
                                    | true =>
                                      exact core_witness_5 s h0 h1 h3 h4 h6 h11 h12 h13 h15 h17 h18
                                  | true =>
                                    exact core_witness_3 s h0 h1 h3 h4 h6 h7 h8 h10 h11 h13 h15
                      | true =>
                        cases h14 : s 14 with
                        | false =>
                          cases h3 : s 3 with
                          | false =>
                            exact color_witness_166 s h3 h9 h14
                          | true =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_164 s h6 h9 h14
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                exact color_witness_146 s h9 h13 h14
                              | true =>
                                cases h10 : s 10 with
                                | false =>
                                  cases h18 : s 18 with
                                  | false =>
                                    exact color_witness_27 s h9 h10 h14 h18
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_88 s h9 h14 h15 h16
                                      | true =>
                                        exact core_witness_8 s h0 h2 h3 h5 h6 h11 h12 h13 h16 h17 h18
                                    | true =>
                                      exact core_witness_5 s h0 h1 h3 h4 h6 h11 h12 h13 h15 h17 h18
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_88 s h9 h14 h15 h16
                                    | true =>
                                      exact core_witness_6 s h0 h2 h3 h5 h6 h7 h8 h10 h11 h13 h16
                                  | true =>
                                    exact core_witness_3 s h0 h1 h3 h4 h6 h7 h8 h10 h11 h13 h15
                        | true =>
                          exact core_witness_0 s h0 h1 h2 h4 h5 h14
    | true =>
      cases h12 : s 12 with
      | false =>
        cases h8 : s 8 with
        | false =>
          cases h10 : s 10 with
          | false =>
            cases h0 : s 0 with
            | false =>
              exact color_witness_202 s h0 h10 h12
            | true =>
              cases h1 : s 1 with
              | false =>
                exact color_witness_201 s h1 h10 h12
              | true =>
                cases h4 : s 4 with
                | false =>
                  exact color_witness_199 s h4 h10 h12
                | true =>
                  cases h2 : s 2 with
                  | false =>
                    exact color_witness_200 s h2 h10 h12
                  | true =>
                    cases h5 : s 5 with
                    | false =>
                      exact color_witness_198 s h5 h10 h12
                    | true =>
                      cases h14 : s 14 with
                      | false =>
                        exact color_witness_148 s h10 h12 h14
                      | true =>
                        exact core_witness_0 s h0 h1 h2 h4 h5 h14
          | true =>
            cases h13 : s 13 with
            | false =>
              cases h18 : s 18 with
              | false =>
                cases h0 : s 0 with
                | false =>
                  exact color_witness_34 s h0 h12 h13 h18
                | true =>
                  cases h1 : s 1 with
                  | false =>
                    exact color_witness_33 s h1 h12 h13 h18
                  | true =>
                    cases h4 : s 4 with
                    | false =>
                      exact color_witness_31 s h4 h12 h13 h18
                    | true =>
                      cases h2 : s 2 with
                      | false =>
                        exact color_witness_32 s h2 h12 h13 h18
                      | true =>
                        cases h5 : s 5 with
                        | false =>
                          exact color_witness_30 s h5 h12 h13 h18
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            exact color_witness_25 s h12 h13 h14 h18
                          | true =>
                            exact core_witness_0 s h0 h1 h2 h4 h5 h14
              | true =>
                cases h11 : s 11 with
                | false =>
                  cases h0 : s 0 with
                  | false =>
                    exact color_witness_197 s h0 h8 h13
                  | true =>
                    cases h1 : s 1 with
                    | false =>
                      exact color_witness_196 s h1 h8 h13
                    | true =>
                      cases h4 : s 4 with
                      | false =>
                        exact color_witness_194 s h4 h8 h13
                      | true =>
                        cases h2 : s 2 with
                        | false =>
                          exact color_witness_195 s h2 h8 h13
                        | true =>
                          cases h5 : s 5 with
                          | false =>
                            exact color_witness_193 s h5 h8 h13
                          | true =>
                            cases h14 : s 14 with
                            | false =>
                              exact color_witness_147 s h8 h13 h14
                            | true =>
                              exact core_witness_0 s h0 h1 h2 h4 h5 h14
                | true =>
                  cases h0 : s 0 with
                  | false =>
                    exact color_witness_197 s h0 h8 h13
                  | true =>
                    cases h1 : s 1 with
                    | false =>
                      exact color_witness_196 s h1 h8 h13
                    | true =>
                      cases h4 : s 4 with
                      | false =>
                        exact color_witness_194 s h4 h8 h13
                      | true =>
                        cases h2 : s 2 with
                        | false =>
                          exact color_witness_195 s h2 h8 h13
                        | true =>
                          cases h5 : s 5 with
                          | false =>
                            exact color_witness_193 s h5 h8 h13
                          | true =>
                            cases h14 : s 14 with
                            | false =>
                              exact color_witness_147 s h8 h13 h14
                            | true =>
                              exact core_witness_0 s h0 h1 h2 h4 h5 h14
            | true =>
              cases h18 : s 18 with
              | false =>
                cases h17 : s 17 with
                | false =>
                  cases h0 : s 0 with
                  | false =>
                    exact color_witness_49 s h0 h8 h18
                  | true =>
                    cases h1 : s 1 with
                    | false =>
                      exact color_witness_48 s h1 h8 h18
                    | true =>
                      cases h4 : s 4 with
                      | false =>
                        exact color_witness_46 s h4 h8 h18
                      | true =>
                        cases h2 : s 2 with
                        | false =>
                          exact color_witness_47 s h2 h8 h18
                        | true =>
                          cases h5 : s 5 with
                          | false =>
                            exact color_witness_45 s h5 h8 h18
                          | true =>
                            cases h14 : s 14 with
                            | false =>
                              exact color_witness_28 s h8 h14 h18
                            | true =>
                              exact core_witness_0 s h0 h1 h2 h4 h5 h14
                | true =>
                  cases h0 : s 0 with
                  | false =>
                    exact color_witness_49 s h0 h8 h18
                  | true =>
                    cases h1 : s 1 with
                    | false =>
                      exact color_witness_48 s h1 h8 h18
                    | true =>
                      cases h4 : s 4 with
                      | false =>
                        exact color_witness_46 s h4 h8 h18
                      | true =>
                        cases h2 : s 2 with
                        | false =>
                          exact color_witness_47 s h2 h8 h18
                        | true =>
                          cases h5 : s 5 with
                          | false =>
                            exact color_witness_45 s h5 h8 h18
                          | true =>
                            cases h14 : s 14 with
                            | false =>
                              exact color_witness_28 s h8 h14 h18
                            | true =>
                              exact core_witness_0 s h0 h1 h2 h4 h5 h14
              | true =>
                cases h0 : s 0 with
                | false =>
                  exact color_witness_212 s h0 h8 h12
                | true =>
                  cases h1 : s 1 with
                  | false =>
                    exact color_witness_211 s h1 h8 h12
                  | true =>
                    cases h4 : s 4 with
                    | false =>
                      exact color_witness_209 s h4 h8 h12
                    | true =>
                      cases h2 : s 2 with
                      | false =>
                        exact color_witness_210 s h2 h8 h12
                      | true =>
                        cases h5 : s 5 with
                        | false =>
                          exact color_witness_208 s h5 h8 h12
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            exact color_witness_150 s h8 h12 h14
                          | true =>
                            exact core_witness_0 s h0 h1 h2 h4 h5 h14
        | true =>
          cases h11 : s 11 with
          | false =>
            cases h17 : s 17 with
            | false =>
              cases h13 : s 13 with
              | false =>
                cases h18 : s 18 with
                | false =>
                  cases h0 : s 0 with
                  | false =>
                    exact color_witness_34 s h0 h12 h13 h18
                  | true =>
                    cases h1 : s 1 with
                    | false =>
                      exact color_witness_33 s h1 h12 h13 h18
                    | true =>
                      cases h4 : s 4 with
                      | false =>
                        exact color_witness_31 s h4 h12 h13 h18
                      | true =>
                        cases h2 : s 2 with
                        | false =>
                          exact color_witness_32 s h2 h12 h13 h18
                        | true =>
                          cases h5 : s 5 with
                          | false =>
                            exact color_witness_30 s h5 h12 h13 h18
                          | true =>
                            cases h14 : s 14 with
                            | false =>
                              exact color_witness_25 s h12 h13 h14 h18
                            | true =>
                              exact core_witness_0 s h0 h1 h2 h4 h5 h14
                | true =>
                  cases h10 : s 10 with
                  | false =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_64 s h0 h13 h17
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_63 s h1 h13 h17
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_61 s h4 h13 h17
                        | true =>
                          cases h2 : s 2 with
                          | false =>
                            exact color_witness_62 s h2 h13 h17
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_60 s h5 h13 h17
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_55 s h13 h14 h17
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
                  | true =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_64 s h0 h13 h17
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_63 s h1 h13 h17
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_61 s h4 h13 h17
                        | true =>
                          cases h2 : s 2 with
                          | false =>
                            exact color_witness_62 s h2 h13 h17
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_60 s h5 h13 h17
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_55 s h13 h14 h17
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
              | true =>
                cases h10 : s 10 with
                | false =>
                  cases h18 : s 18 with
                  | false =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_39 s h0 h11 h18
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_38 s h1 h11 h18
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_36 s h4 h11 h18
                        | true =>
                          cases h2 : s 2 with
                          | false =>
                            exact color_witness_37 s h2 h11 h18
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_35 s h5 h11 h18
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_26 s h11 h14 h18
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
                  | true =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_69 s h0 h11 h12 h17
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_68 s h1 h11 h12 h17
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_66 s h4 h11 h12 h17
                        | true =>
                          cases h2 : s 2 with
                          | false =>
                            exact color_witness_67 s h2 h11 h12 h17
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_65 s h5 h11 h12 h17
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_56 s h11 h12 h14 h17
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
                | true =>
                  cases h18 : s 18 with
                  | false =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_39 s h0 h11 h18
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_38 s h1 h11 h18
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_36 s h4 h11 h18
                        | true =>
                          cases h2 : s 2 with
                          | false =>
                            exact color_witness_37 s h2 h11 h18
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_35 s h5 h11 h18
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_26 s h11 h14 h18
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
                  | true =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_69 s h0 h11 h12 h17
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_68 s h1 h11 h12 h17
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_66 s h4 h11 h12 h17
                        | true =>
                          cases h2 : s 2 with
                          | false =>
                            exact color_witness_67 s h2 h11 h12 h17
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_65 s h5 h11 h12 h17
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_56 s h11 h12 h14 h17
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
            | true =>
              cases h13 : s 13 with
              | false =>
                cases h0 : s 0 with
                | false =>
                  cases h14 : s 14 with
                  | false =>
                    exact color_witness_144 s h0 h11 h13 h14
                  | true =>
                    cases h1 : s 1 with
                    | false =>
                      cases h4 : s 4 with
                      | false =>
                        exact color_witness_182 s h0 h1 h4 h11 h13
                      | true =>
                        cases h5 : s 5 with
                        | false =>
                          exact color_witness_179 s h1 h5 h11 h13
                        | true =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_201 s h1 h10 h12
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_33 s h1 h12 h13 h18
                            | true =>
                              cases h16 : s 16 with
                              | false =>
                                exact color_witness_93 s h1 h11 h13 h16
                              | true =>
                                cases h6 : s 6 with
                                | false =>
                                  exact color_witness_176 s h1 h6 h11 h13
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_119 s h0 h11 h13 h15
                                  | true =>
                                    exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
                    | true =>
                      cases h2 : s 2 with
                      | false =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_181 s h2 h4 h11 h13
                        | true =>
                          cases h5 : s 5 with
                          | false =>
                            exact color_witness_178 s h0 h2 h5 h11 h13
                          | true =>
                            cases h10 : s 10 with
                            | false =>
                              exact color_witness_200 s h2 h10 h12
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_118 s h2 h11 h13 h15
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_32 s h2 h12 h13 h18
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_175 s h2 h6 h11 h13
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_94 s h0 h11 h13 h16
                                    | true =>
                                      exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_199 s h4 h10 h12
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_31 s h4 h12 h13 h18
                            | true =>
                              cases h16 : s 16 with
                              | false =>
                                exact color_witness_91 s h4 h11 h13 h16
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  exact color_witness_180 s h3 h4 h11 h13
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_119 s h0 h11 h13 h15
                                  | true =>
                                    exact core_witness_10 s h1 h2 h3 h8 h9 h10 h14 h15 h16 h17 h18
                        | true =>
                          cases h5 : s 5 with
                          | false =>
                            cases h10 : s 10 with
                            | false =>
                              exact color_witness_198 s h5 h10 h12
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_116 s h5 h11 h13 h15
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_30 s h5 h12 h13 h18
                                | true =>
                                  cases h3 : s 3 with
                                  | false =>
                                    exact color_witness_177 s h3 h5 h11 h13
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_94 s h0 h11 h13 h16
                                    | true =>
                                      exact core_witness_10 s h1 h2 h3 h8 h9 h10 h14 h15 h16 h17 h18
                          | true =>
                            cases h10 : s 10 with
                            | false =>
                              exact color_witness_202 s h0 h10 h12
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_119 s h0 h11 h13 h15
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_94 s h0 h11 h13 h16
                                | true =>
                                  cases h18 : s 18 with
                                  | false =>
                                    exact color_witness_34 s h0 h12 h13 h18
                                  | true =>
                                    cases h3 : s 3 with
                                    | false =>
                                      cases h6 : s 6 with
                                      | false =>
                                        exact color_witness_174 s h0 h3 h6 h11 h13
                                      | true =>
                                        exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
                                    | true =>
                                      exact core_witness_10 s h1 h2 h3 h8 h9 h10 h14 h15 h16 h17 h18
                | true =>
                  cases h1 : s 1 with
                  | false =>
                    cases h5 : s 5 with
                    | false =>
                      exact color_witness_179 s h1 h5 h11 h13
                    | true =>
                      cases h2 : s 2 with
                      | false =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_181 s h2 h4 h11 h13
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            exact color_witness_143 s h1 h2 h11 h13 h14
                          | true =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_175 s h2 h6 h11 h13
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_200 s h2 h10 h12
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_32 s h2 h12 h13 h18
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_118 s h2 h11 h13 h15
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_93 s h1 h11 h13 h16
                                    | true =>
                                      exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_199 s h4 h10 h12
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_31 s h4 h12 h13 h18
                            | true =>
                              cases h16 : s 16 with
                              | false =>
                                exact color_witness_91 s h4 h11 h13 h16
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  exact color_witness_180 s h3 h4 h11 h13
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_176 s h1 h6 h11 h13
                                  | true =>
                                    exact core_witness_7 s h0 h2 h3 h5 h6 h8 h9 h10 h16 h17 h18
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_140 s h6 h11 h13 h14
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_148 s h10 h12 h14
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_25 s h12 h13 h14 h18
                                | true =>
                                  cases h3 : s 3 with
                                  | false =>
                                    exact color_witness_142 s h3 h11 h13 h14
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_93 s h1 h11 h13 h16
                                    | true =>
                                      exact core_witness_7 s h0 h2 h3 h5 h6 h8 h9 h10 h16 h17 h18
                          | true =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_176 s h1 h6 h11 h13
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_201 s h1 h10 h12
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_93 s h1 h11 h13 h16
                                | true =>
                                  cases h18 : s 18 with
                                  | false =>
                                    exact color_witness_33 s h1 h12 h13 h18
                                  | true =>
                                    cases h3 : s 3 with
                                    | false =>
                                      cases h15 : s 15 with
                                      | false =>
                                        exact color_witness_117 s h1 h3 h11 h13 h15
                                      | true =>
                                        exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
                                    | true =>
                                      exact core_witness_7 s h0 h2 h3 h5 h6 h8 h9 h10 h16 h17 h18
                  | true =>
                    cases h4 : s 4 with
                    | false =>
                      cases h2 : s 2 with
                      | false =>
                        exact color_witness_181 s h2 h4 h11 h13
                      | true =>
                        cases h5 : s 5 with
                        | false =>
                          cases h14 : s 14 with
                          | false =>
                            exact color_witness_141 s h4 h5 h11 h13 h14
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_177 s h3 h5 h11 h13
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_198 s h5 h10 h12
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_30 s h5 h12 h13 h18
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_116 s h5 h11 h13 h15
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_91 s h4 h11 h13 h16
                                    | true =>
                                      exact core_witness_10 s h1 h2 h3 h8 h9 h10 h14 h15 h16 h17 h18
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_142 s h3 h11 h13 h14
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_148 s h10 h12 h14
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_25 s h12 h13 h14 h18
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_140 s h6 h11 h13 h14
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_91 s h4 h11 h13 h16
                                    | true =>
                                      exact core_witness_7 s h0 h2 h3 h5 h6 h8 h9 h10 h16 h17 h18
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_180 s h3 h4 h11 h13
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_199 s h4 h10 h12
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_91 s h4 h11 h13 h16
                                | true =>
                                  cases h18 : s 18 with
                                  | false =>
                                    exact color_witness_31 s h4 h12 h13 h18
                                  | true =>
                                    cases h6 : s 6 with
                                    | false =>
                                      cases h15 : s 15 with
                                      | false =>
                                        exact color_witness_115 s h4 h6 h11 h13 h15
                                      | true =>
                                        exact core_witness_10 s h1 h2 h3 h8 h9 h10 h14 h15 h16 h17 h18
                                    | true =>
                                      exact core_witness_7 s h0 h2 h3 h5 h6 h8 h9 h10 h16 h17 h18
                    | true =>
                      cases h2 : s 2 with
                      | false =>
                        cases h5 : s 5 with
                        | false =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_198 s h5 h10 h12
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_30 s h5 h12 h13 h18
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_116 s h5 h11 h13 h15
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  exact color_witness_177 s h3 h5 h11 h13
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_175 s h2 h6 h11 h13
                                  | true =>
                                    exact core_witness_4 s h0 h1 h3 h4 h6 h8 h9 h10 h15 h17 h18
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_140 s h6 h11 h13 h14
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_148 s h10 h12 h14
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_25 s h12 h13 h14 h18
                                | true =>
                                  cases h3 : s 3 with
                                  | false =>
                                    exact color_witness_142 s h3 h11 h13 h14
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      exact color_witness_118 s h2 h11 h13 h15
                                    | true =>
                                      exact core_witness_4 s h0 h1 h3 h4 h6 h8 h9 h10 h15 h17 h18
                          | true =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_175 s h2 h6 h11 h13
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_200 s h2 h10 h12
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  exact color_witness_118 s h2 h11 h13 h15
                                | true =>
                                  cases h18 : s 18 with
                                  | false =>
                                    exact color_witness_32 s h2 h12 h13 h18
                                  | true =>
                                    cases h3 : s 3 with
                                    | false =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_92 s h2 h3 h11 h13 h16
                                      | true =>
                                        exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
                                    | true =>
                                      exact core_witness_4 s h0 h1 h3 h4 h6 h8 h9 h10 h15 h17 h18
                      | true =>
                        cases h5 : s 5 with
                        | false =>
                          cases h14 : s 14 with
                          | false =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_142 s h3 h11 h13 h14
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_148 s h10 h12 h14
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_25 s h12 h13 h14 h18
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_140 s h6 h11 h13 h14
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      exact color_witness_116 s h5 h11 h13 h15
                                    | true =>
                                      exact core_witness_4 s h0 h1 h3 h4 h6 h8 h9 h10 h15 h17 h18
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_177 s h3 h5 h11 h13
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_198 s h5 h10 h12
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  exact color_witness_116 s h5 h11 h13 h15
                                | true =>
                                  cases h18 : s 18 with
                                  | false =>
                                    exact color_witness_30 s h5 h12 h13 h18
                                  | true =>
                                    cases h6 : s 6 with
                                    | false =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_90 s h5 h6 h11 h13 h16
                                      | true =>
                                        exact core_witness_10 s h1 h2 h3 h8 h9 h10 h14 h15 h16 h17 h18
                                    | true =>
                                      exact core_witness_4 s h0 h1 h3 h4 h6 h8 h9 h10 h15 h17 h18
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_142 s h3 h11 h13 h14
                            | true =>
                              cases h6 : s 6 with
                              | false =>
                                exact color_witness_140 s h6 h11 h13 h14
                              | true =>
                                cases h10 : s 10 with
                                | false =>
                                  exact color_witness_148 s h10 h12 h14
                                | true =>
                                  cases h18 : s 18 with
                                  | false =>
                                    exact color_witness_25 s h12 h13 h14 h18
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_85 s h11 h13 h14 h15 h16
                                      | true =>
                                        exact core_witness_7 s h0 h2 h3 h5 h6 h8 h9 h10 h16 h17 h18
                                    | true =>
                                      exact core_witness_4 s h0 h1 h3 h4 h6 h8 h9 h10 h15 h17 h18
                          | true =>
                            exact core_witness_0 s h0 h1 h2 h4 h5 h14
              | true =>
                cases h10 : s 10 with
                | false =>
                  cases h0 : s 0 with
                  | false =>
                    exact color_witness_202 s h0 h10 h12
                  | true =>
                    cases h1 : s 1 with
                    | false =>
                      exact color_witness_201 s h1 h10 h12
                    | true =>
                      cases h4 : s 4 with
                      | false =>
                        exact color_witness_199 s h4 h10 h12
                      | true =>
                        cases h2 : s 2 with
                        | false =>
                          exact color_witness_200 s h2 h10 h12
                        | true =>
                          cases h5 : s 5 with
                          | false =>
                            exact color_witness_198 s h5 h10 h12
                          | true =>
                            cases h14 : s 14 with
                            | false =>
                              exact color_witness_148 s h10 h12 h14
                            | true =>
                              exact core_witness_0 s h0 h1 h2 h4 h5 h14
                | true =>
                  cases h18 : s 18 with
                  | false =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_39 s h0 h11 h18
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_38 s h1 h11 h18
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_36 s h4 h11 h18
                        | true =>
                          cases h2 : s 2 with
                          | false =>
                            exact color_witness_37 s h2 h11 h18
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_35 s h5 h11 h18
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_26 s h11 h14 h18
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
                  | true =>
                    cases h0 : s 0 with
                    | false =>
                      cases h14 : s 14 with
                      | false =>
                        exact color_witness_155 s h0 h12 h14
                      | true =>
                        cases h15 : s 15 with
                        | false =>
                          exact color_witness_124 s h0 h12 h15
                        | true =>
                          cases h16 : s 16 with
                          | false =>
                            exact color_witness_99 s h0 h12 h16
                          | true =>
                            cases h1 : s 1 with
                            | false =>
                              cases h4 : s 4 with
                              | false =>
                                exact color_witness_221 s h0 h1 h4 h12
                              | true =>
                                cases h5 : s 5 with
                                | false =>
                                  exact color_witness_218 s h1 h5 h12
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_215 s h1 h6 h12
                                  | true =>
                                    exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
                            | true =>
                              cases h2 : s 2 with
                              | false =>
                                cases h4 : s 4 with
                                | false =>
                                  exact color_witness_220 s h2 h4 h12
                                | true =>
                                  cases h5 : s 5 with
                                  | false =>
                                    exact color_witness_217 s h0 h2 h5 h12
                                  | true =>
                                    cases h6 : s 6 with
                                    | false =>
                                      exact color_witness_214 s h2 h6 h12
                                    | true =>
                                      exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  cases h4 : s 4 with
                                  | false =>
                                    exact color_witness_219 s h3 h4 h12
                                  | true =>
                                    cases h5 : s 5 with
                                    | false =>
                                      exact color_witness_216 s h3 h5 h12
                                    | true =>
                                      cases h6 : s 6 with
                                      | false =>
                                        exact color_witness_213 s h0 h3 h6 h12
                                      | true =>
                                        exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
                                | true =>
                                  exact core_witness_10 s h1 h2 h3 h8 h9 h10 h14 h15 h16 h17 h18
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        cases h5 : s 5 with
                        | false =>
                          exact color_witness_218 s h1 h5 h12
                        | true =>
                          cases h6 : s 6 with
                          | false =>
                            exact color_witness_215 s h1 h6 h12
                          | true =>
                            cases h16 : s 16 with
                            | false =>
                              exact color_witness_98 s h1 h12 h16
                            | true =>
                              cases h2 : s 2 with
                              | false =>
                                cases h4 : s 4 with
                                | false =>
                                  exact color_witness_220 s h2 h4 h12
                                | true =>
                                  cases h14 : s 14 with
                                  | false =>
                                    exact color_witness_154 s h1 h2 h12 h14
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      exact color_witness_123 s h2 h12 h15
                                    | true =>
                                      exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  cases h4 : s 4 with
                                  | false =>
                                    exact color_witness_219 s h3 h4 h12
                                  | true =>
                                    cases h14 : s 14 with
                                    | false =>
                                      exact color_witness_153 s h3 h12 h14
                                    | true =>
                                      cases h15 : s 15 with
                                      | false =>
                                        exact color_witness_122 s h1 h3 h12 h15
                                      | true =>
                                        exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
                                | true =>
                                  exact core_witness_7 s h0 h2 h3 h5 h6 h8 h9 h10 h16 h17 h18
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          cases h2 : s 2 with
                          | false =>
                            exact color_witness_220 s h2 h4 h12
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_219 s h3 h4 h12
                            | true =>
                              cases h16 : s 16 with
                              | false =>
                                exact color_witness_96 s h4 h12 h16
                              | true =>
                                cases h5 : s 5 with
                                | false =>
                                  cases h14 : s 14 with
                                  | false =>
                                    exact color_witness_152 s h4 h5 h12 h14
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      exact color_witness_121 s h5 h12 h15
                                    | true =>
                                      exact core_witness_10 s h1 h2 h3 h8 h9 h10 h14 h15 h16 h17 h18
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    cases h14 : s 14 with
                                    | false =>
                                      exact color_witness_151 s h6 h12 h14
                                    | true =>
                                      cases h15 : s 15 with
                                      | false =>
                                        exact color_witness_120 s h4 h6 h12 h15
                                      | true =>
                                        exact core_witness_10 s h1 h2 h3 h8 h9 h10 h14 h15 h16 h17 h18
                                  | true =>
                                    exact core_witness_7 s h0 h2 h3 h5 h6 h8 h9 h10 h16 h17 h18
                        | true =>
                          cases h2 : s 2 with
                          | false =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_214 s h2 h6 h12
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_123 s h2 h12 h15
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  cases h5 : s 5 with
                                  | false =>
                                    exact color_witness_216 s h3 h5 h12
                                  | true =>
                                    cases h14 : s 14 with
                                    | false =>
                                      exact color_witness_153 s h3 h12 h14
                                    | true =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_97 s h2 h3 h12 h16
                                      | true =>
                                        exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
                                | true =>
                                  exact core_witness_4 s h0 h1 h3 h4 h6 h8 h9 h10 h15 h17 h18
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              cases h3 : s 3 with
                              | false =>
                                exact color_witness_216 s h3 h5 h12
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  exact color_witness_121 s h5 h12 h15
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    cases h14 : s 14 with
                                    | false =>
                                      exact color_witness_151 s h6 h12 h14
                                    | true =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_95 s h5 h6 h12 h16
                                      | true =>
                                        exact core_witness_10 s h1 h2 h3 h8 h9 h10 h14 h15 h16 h17 h18
                                  | true =>
                                    exact core_witness_4 s h0 h1 h3 h4 h6 h8 h9 h10 h15 h17 h18
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                cases h3 : s 3 with
                                | false =>
                                  exact color_witness_153 s h3 h12 h14
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_151 s h6 h12 h14
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_86 s h12 h14 h15 h16
                                      | true =>
                                        exact core_witness_7 s h0 h2 h3 h5 h6 h8 h9 h10 h16 h17 h18
                                    | true =>
                                      exact core_witness_4 s h0 h1 h3 h4 h6 h8 h9 h10 h15 h17 h18
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
          | true =>
            cases h17 : s 17 with
            | false =>
              cases h18 : s 18 with
              | false =>
                cases h0 : s 0 with
                | false =>
                  cases h14 : s 14 with
                  | false =>
                    exact color_witness_15 s h0 h14 h17 h18
                  | true =>
                    cases h1 : s 1 with
                    | false =>
                      cases h4 : s 4 with
                      | false =>
                        exact color_witness_24 s h0 h1 h4 h17 h18
                      | true =>
                        cases h5 : s 5 with
                        | false =>
                          exact color_witness_21 s h1 h5 h17 h18
                        | true =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_73 s h1 h10 h17
                          | true =>
                            cases h13 : s 13 with
                            | false =>
                              exact color_witness_33 s h1 h12 h13 h18
                            | true =>
                              cases h16 : s 16 with
                              | false =>
                                exact color_witness_4 s h1 h16 h17 h18
                              | true =>
                                cases h6 : s 6 with
                                | false =>
                                  exact color_witness_18 s h1 h6 h17 h18
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_10 s h0 h15 h17 h18
                                  | true =>
                                    exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
                    | true =>
                      cases h2 : s 2 with
                      | false =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_23 s h2 h4 h17 h18
                        | true =>
                          cases h5 : s 5 with
                          | false =>
                            exact color_witness_20 s h0 h2 h5 h17 h18
                          | true =>
                            cases h10 : s 10 with
                            | false =>
                              exact color_witness_72 s h2 h10 h17
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                exact color_witness_32 s h2 h12 h13 h18
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  exact color_witness_9 s h2 h15 h17 h18
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_17 s h2 h6 h17 h18
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_5 s h0 h16 h17 h18
                                    | true =>
                                      exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_71 s h4 h10 h17
                          | true =>
                            cases h13 : s 13 with
                            | false =>
                              exact color_witness_31 s h4 h12 h13 h18
                            | true =>
                              cases h16 : s 16 with
                              | false =>
                                exact color_witness_2 s h4 h16 h17 h18
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  exact color_witness_22 s h3 h4 h17 h18
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_10 s h0 h15 h17 h18
                                  | true =>
                                    exact core_witness_9 s h1 h2 h3 h7 h8 h10 h11 h13 h14 h15 h16
                        | true =>
                          cases h5 : s 5 with
                          | false =>
                            cases h10 : s 10 with
                            | false =>
                              exact color_witness_70 s h5 h10 h17
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                exact color_witness_30 s h5 h12 h13 h18
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  exact color_witness_7 s h5 h15 h17 h18
                                | true =>
                                  cases h3 : s 3 with
                                  | false =>
                                    exact color_witness_19 s h3 h5 h17 h18
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_5 s h0 h16 h17 h18
                                    | true =>
                                      exact core_witness_9 s h1 h2 h3 h7 h8 h10 h11 h13 h14 h15 h16
                          | true =>
                            cases h10 : s 10 with
                            | false =>
                              exact color_witness_74 s h0 h10 h17
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                exact color_witness_34 s h0 h12 h13 h18
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  exact color_witness_10 s h0 h15 h17 h18
                                | true =>
                                  cases h16 : s 16 with
                                  | false =>
                                    exact color_witness_5 s h0 h16 h17 h18
                                  | true =>
                                    cases h3 : s 3 with
                                    | false =>
                                      cases h6 : s 6 with
                                      | false =>
                                        exact color_witness_16 s h0 h3 h6 h17 h18
                                      | true =>
                                        exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
                                    | true =>
                                      exact core_witness_9 s h1 h2 h3 h7 h8 h10 h11 h13 h14 h15 h16
                | true =>
                  cases h1 : s 1 with
                  | false =>
                    cases h5 : s 5 with
                    | false =>
                      exact color_witness_21 s h1 h5 h17 h18
                    | true =>
                      cases h2 : s 2 with
                      | false =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_23 s h2 h4 h17 h18
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            exact color_witness_14 s h1 h2 h14 h17 h18
                          | true =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_17 s h2 h6 h17 h18
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_72 s h2 h10 h17
                              | true =>
                                cases h13 : s 13 with
                                | false =>
                                  exact color_witness_32 s h2 h12 h13 h18
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_9 s h2 h15 h17 h18
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_4 s h1 h16 h17 h18
                                    | true =>
                                      exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_71 s h4 h10 h17
                          | true =>
                            cases h13 : s 13 with
                            | false =>
                              exact color_witness_31 s h4 h12 h13 h18
                            | true =>
                              cases h16 : s 16 with
                              | false =>
                                exact color_witness_2 s h4 h16 h17 h18
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  exact color_witness_22 s h3 h4 h17 h18
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_18 s h1 h6 h17 h18
                                  | true =>
                                    exact core_witness_6 s h0 h2 h3 h5 h6 h7 h8 h10 h11 h13 h16
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_11 s h6 h14 h17 h18
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_57 s h10 h14 h17
                              | true =>
                                cases h13 : s 13 with
                                | false =>
                                  exact color_witness_25 s h12 h13 h14 h18
                                | true =>
                                  cases h3 : s 3 with
                                  | false =>
                                    exact color_witness_13 s h3 h14 h17 h18
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_4 s h1 h16 h17 h18
                                    | true =>
                                      exact core_witness_6 s h0 h2 h3 h5 h6 h7 h8 h10 h11 h13 h16
                          | true =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_18 s h1 h6 h17 h18
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_73 s h1 h10 h17
                              | true =>
                                cases h13 : s 13 with
                                | false =>
                                  exact color_witness_33 s h1 h12 h13 h18
                                | true =>
                                  cases h16 : s 16 with
                                  | false =>
                                    exact color_witness_4 s h1 h16 h17 h18
                                  | true =>
                                    cases h3 : s 3 with
                                    | false =>
                                      cases h15 : s 15 with
                                      | false =>
                                        exact color_witness_8 s h1 h3 h15 h17 h18
                                      | true =>
                                        exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
                                    | true =>
                                      exact core_witness_6 s h0 h2 h3 h5 h6 h7 h8 h10 h11 h13 h16
                  | true =>
                    cases h4 : s 4 with
                    | false =>
                      cases h2 : s 2 with
                      | false =>
                        exact color_witness_23 s h2 h4 h17 h18
                      | true =>
                        cases h5 : s 5 with
                        | false =>
                          cases h14 : s 14 with
                          | false =>
                            exact color_witness_12 s h4 h5 h14 h17 h18
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_19 s h3 h5 h17 h18
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_70 s h5 h10 h17
                              | true =>
                                cases h13 : s 13 with
                                | false =>
                                  exact color_witness_30 s h5 h12 h13 h18
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_7 s h5 h15 h17 h18
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_2 s h4 h16 h17 h18
                                    | true =>
                                      exact core_witness_9 s h1 h2 h3 h7 h8 h10 h11 h13 h14 h15 h16
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_13 s h3 h14 h17 h18
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_57 s h10 h14 h17
                              | true =>
                                cases h13 : s 13 with
                                | false =>
                                  exact color_witness_25 s h12 h13 h14 h18
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_11 s h6 h14 h17 h18
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_2 s h4 h16 h17 h18
                                    | true =>
                                      exact core_witness_6 s h0 h2 h3 h5 h6 h7 h8 h10 h11 h13 h16
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_22 s h3 h4 h17 h18
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_71 s h4 h10 h17
                              | true =>
                                cases h13 : s 13 with
                                | false =>
                                  exact color_witness_31 s h4 h12 h13 h18
                                | true =>
                                  cases h16 : s 16 with
                                  | false =>
                                    exact color_witness_2 s h4 h16 h17 h18
                                  | true =>
                                    cases h6 : s 6 with
                                    | false =>
                                      cases h15 : s 15 with
                                      | false =>
                                        exact color_witness_6 s h4 h6 h15 h17 h18
                                      | true =>
                                        exact core_witness_9 s h1 h2 h3 h7 h8 h10 h11 h13 h14 h15 h16
                                    | true =>
                                      exact core_witness_6 s h0 h2 h3 h5 h6 h7 h8 h10 h11 h13 h16
                    | true =>
                      cases h2 : s 2 with
                      | false =>
                        cases h5 : s 5 with
                        | false =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_70 s h5 h10 h17
                          | true =>
                            cases h13 : s 13 with
                            | false =>
                              exact color_witness_30 s h5 h12 h13 h18
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_7 s h5 h15 h17 h18
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  exact color_witness_19 s h3 h5 h17 h18
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_17 s h2 h6 h17 h18
                                  | true =>
                                    exact core_witness_3 s h0 h1 h3 h4 h6 h7 h8 h10 h11 h13 h15
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_11 s h6 h14 h17 h18
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_57 s h10 h14 h17
                              | true =>
                                cases h13 : s 13 with
                                | false =>
                                  exact color_witness_25 s h12 h13 h14 h18
                                | true =>
                                  cases h3 : s 3 with
                                  | false =>
                                    exact color_witness_13 s h3 h14 h17 h18
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      exact color_witness_9 s h2 h15 h17 h18
                                    | true =>
                                      exact core_witness_3 s h0 h1 h3 h4 h6 h7 h8 h10 h11 h13 h15
                          | true =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_17 s h2 h6 h17 h18
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_72 s h2 h10 h17
                              | true =>
                                cases h13 : s 13 with
                                | false =>
                                  exact color_witness_32 s h2 h12 h13 h18
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_9 s h2 h15 h17 h18
                                  | true =>
                                    cases h3 : s 3 with
                                    | false =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_3 s h2 h3 h16 h17 h18
                                      | true =>
                                        exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
                                    | true =>
                                      exact core_witness_3 s h0 h1 h3 h4 h6 h7 h8 h10 h11 h13 h15
                      | true =>
                        cases h5 : s 5 with
                        | false =>
                          cases h14 : s 14 with
                          | false =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_13 s h3 h14 h17 h18
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_57 s h10 h14 h17
                              | true =>
                                cases h13 : s 13 with
                                | false =>
                                  exact color_witness_25 s h12 h13 h14 h18
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_11 s h6 h14 h17 h18
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      exact color_witness_7 s h5 h15 h17 h18
                                    | true =>
                                      exact core_witness_3 s h0 h1 h3 h4 h6 h7 h8 h10 h11 h13 h15
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_19 s h3 h5 h17 h18
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_70 s h5 h10 h17
                              | true =>
                                cases h13 : s 13 with
                                | false =>
                                  exact color_witness_30 s h5 h12 h13 h18
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_7 s h5 h15 h17 h18
                                  | true =>
                                    cases h6 : s 6 with
                                    | false =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_1 s h5 h6 h16 h17 h18
                                      | true =>
                                        exact core_witness_9 s h1 h2 h3 h7 h8 h10 h11 h13 h14 h15 h16
                                    | true =>
                                      exact core_witness_3 s h0 h1 h3 h4 h6 h7 h8 h10 h11 h13 h15
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_13 s h3 h14 h17 h18
                            | true =>
                              cases h6 : s 6 with
                              | false =>
                                exact color_witness_11 s h6 h14 h17 h18
                              | true =>
                                cases h10 : s 10 with
                                | false =>
                                  exact color_witness_57 s h10 h14 h17
                                | true =>
                                  cases h13 : s 13 with
                                  | false =>
                                    exact color_witness_25 s h12 h13 h14 h18
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_0 s h14 h15 h16 h17 h18
                                      | true =>
                                        exact core_witness_6 s h0 h2 h3 h5 h6 h7 h8 h10 h11 h13 h16
                                    | true =>
                                      exact core_witness_3 s h0 h1 h3 h4 h6 h7 h8 h10 h11 h13 h15
                          | true =>
                            exact core_witness_0 s h0 h1 h2 h4 h5 h14
              | true =>
                cases h10 : s 10 with
                | false =>
                  cases h0 : s 0 with
                  | false =>
                    exact color_witness_74 s h0 h10 h17
                  | true =>
                    cases h1 : s 1 with
                    | false =>
                      exact color_witness_73 s h1 h10 h17
                    | true =>
                      cases h4 : s 4 with
                      | false =>
                        exact color_witness_71 s h4 h10 h17
                      | true =>
                        cases h2 : s 2 with
                        | false =>
                          exact color_witness_72 s h2 h10 h17
                        | true =>
                          cases h5 : s 5 with
                          | false =>
                            exact color_witness_70 s h5 h10 h17
                          | true =>
                            cases h14 : s 14 with
                            | false =>
                              exact color_witness_57 s h10 h14 h17
                            | true =>
                              exact core_witness_0 s h0 h1 h2 h4 h5 h14
                | true =>
                  cases h13 : s 13 with
                  | false =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_64 s h0 h13 h17
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_63 s h1 h13 h17
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_61 s h4 h13 h17
                        | true =>
                          cases h2 : s 2 with
                          | false =>
                            exact color_witness_62 s h2 h13 h17
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_60 s h5 h13 h17
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_55 s h13 h14 h17
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
                  | true =>
                    cases h0 : s 0 with
                    | false =>
                      cases h14 : s 14 with
                      | false =>
                        exact color_witness_155 s h0 h12 h14
                      | true =>
                        cases h15 : s 15 with
                        | false =>
                          exact color_witness_124 s h0 h12 h15
                        | true =>
                          cases h16 : s 16 with
                          | false =>
                            exact color_witness_99 s h0 h12 h16
                          | true =>
                            cases h1 : s 1 with
                            | false =>
                              cases h4 : s 4 with
                              | false =>
                                exact color_witness_221 s h0 h1 h4 h12
                              | true =>
                                cases h5 : s 5 with
                                | false =>
                                  exact color_witness_218 s h1 h5 h12
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_215 s h1 h6 h12
                                  | true =>
                                    exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
                            | true =>
                              cases h2 : s 2 with
                              | false =>
                                cases h4 : s 4 with
                                | false =>
                                  exact color_witness_220 s h2 h4 h12
                                | true =>
                                  cases h5 : s 5 with
                                  | false =>
                                    exact color_witness_217 s h0 h2 h5 h12
                                  | true =>
                                    cases h6 : s 6 with
                                    | false =>
                                      exact color_witness_214 s h2 h6 h12
                                    | true =>
                                      exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  cases h4 : s 4 with
                                  | false =>
                                    exact color_witness_219 s h3 h4 h12
                                  | true =>
                                    cases h5 : s 5 with
                                    | false =>
                                      exact color_witness_216 s h3 h5 h12
                                    | true =>
                                      cases h6 : s 6 with
                                      | false =>
                                        exact color_witness_213 s h0 h3 h6 h12
                                      | true =>
                                        exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
                                | true =>
                                  exact core_witness_9 s h1 h2 h3 h7 h8 h10 h11 h13 h14 h15 h16
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        cases h5 : s 5 with
                        | false =>
                          exact color_witness_218 s h1 h5 h12
                        | true =>
                          cases h6 : s 6 with
                          | false =>
                            exact color_witness_215 s h1 h6 h12
                          | true =>
                            cases h16 : s 16 with
                            | false =>
                              exact color_witness_98 s h1 h12 h16
                            | true =>
                              cases h2 : s 2 with
                              | false =>
                                cases h4 : s 4 with
                                | false =>
                                  exact color_witness_220 s h2 h4 h12
                                | true =>
                                  cases h14 : s 14 with
                                  | false =>
                                    exact color_witness_154 s h1 h2 h12 h14
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      exact color_witness_123 s h2 h12 h15
                                    | true =>
                                      exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  cases h4 : s 4 with
                                  | false =>
                                    exact color_witness_219 s h3 h4 h12
                                  | true =>
                                    cases h14 : s 14 with
                                    | false =>
                                      exact color_witness_153 s h3 h12 h14
                                    | true =>
                                      cases h15 : s 15 with
                                      | false =>
                                        exact color_witness_122 s h1 h3 h12 h15
                                      | true =>
                                        exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
                                | true =>
                                  exact core_witness_6 s h0 h2 h3 h5 h6 h7 h8 h10 h11 h13 h16
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          cases h2 : s 2 with
                          | false =>
                            exact color_witness_220 s h2 h4 h12
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_219 s h3 h4 h12
                            | true =>
                              cases h16 : s 16 with
                              | false =>
                                exact color_witness_96 s h4 h12 h16
                              | true =>
                                cases h5 : s 5 with
                                | false =>
                                  cases h14 : s 14 with
                                  | false =>
                                    exact color_witness_152 s h4 h5 h12 h14
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      exact color_witness_121 s h5 h12 h15
                                    | true =>
                                      exact core_witness_9 s h1 h2 h3 h7 h8 h10 h11 h13 h14 h15 h16
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    cases h14 : s 14 with
                                    | false =>
                                      exact color_witness_151 s h6 h12 h14
                                    | true =>
                                      cases h15 : s 15 with
                                      | false =>
                                        exact color_witness_120 s h4 h6 h12 h15
                                      | true =>
                                        exact core_witness_9 s h1 h2 h3 h7 h8 h10 h11 h13 h14 h15 h16
                                  | true =>
                                    exact core_witness_6 s h0 h2 h3 h5 h6 h7 h8 h10 h11 h13 h16
                        | true =>
                          cases h2 : s 2 with
                          | false =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_214 s h2 h6 h12
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_123 s h2 h12 h15
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  cases h5 : s 5 with
                                  | false =>
                                    exact color_witness_216 s h3 h5 h12
                                  | true =>
                                    cases h14 : s 14 with
                                    | false =>
                                      exact color_witness_153 s h3 h12 h14
                                    | true =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_97 s h2 h3 h12 h16
                                      | true =>
                                        exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
                                | true =>
                                  exact core_witness_3 s h0 h1 h3 h4 h6 h7 h8 h10 h11 h13 h15
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              cases h3 : s 3 with
                              | false =>
                                exact color_witness_216 s h3 h5 h12
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  exact color_witness_121 s h5 h12 h15
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    cases h14 : s 14 with
                                    | false =>
                                      exact color_witness_151 s h6 h12 h14
                                    | true =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_95 s h5 h6 h12 h16
                                      | true =>
                                        exact core_witness_9 s h1 h2 h3 h7 h8 h10 h11 h13 h14 h15 h16
                                  | true =>
                                    exact core_witness_3 s h0 h1 h3 h4 h6 h7 h8 h10 h11 h13 h15
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                cases h3 : s 3 with
                                | false =>
                                  exact color_witness_153 s h3 h12 h14
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_151 s h6 h12 h14
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_86 s h12 h14 h15 h16
                                      | true =>
                                        exact core_witness_6 s h0 h2 h3 h5 h6 h7 h8 h10 h11 h13 h16
                                    | true =>
                                      exact core_witness_3 s h0 h1 h3 h4 h6 h7 h8 h10 h11 h13 h15
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
            | true =>
              cases h0 : s 0 with
              | false =>
                cases h10 : s 10 with
                | false =>
                  exact color_witness_202 s h0 h10 h12
                | true =>
                  cases h14 : s 14 with
                  | false =>
                    exact color_witness_155 s h0 h12 h14
                  | true =>
                    cases h15 : s 15 with
                    | false =>
                      exact color_witness_124 s h0 h12 h15
                    | true =>
                      cases h16 : s 16 with
                      | false =>
                        exact color_witness_99 s h0 h12 h16
                      | true =>
                        cases h1 : s 1 with
                        | false =>
                          cases h4 : s 4 with
                          | false =>
                            exact color_witness_221 s h0 h1 h4 h12
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_218 s h1 h5 h12
                            | true =>
                              cases h6 : s 6 with
                              | false =>
                                exact color_witness_215 s h1 h6 h12
                              | true =>
                                cases h13 : s 13 with
                                | false =>
                                  cases h18 : s 18 with
                                  | false =>
                                    exact color_witness_33 s h1 h12 h13 h18
                                  | true =>
                                    exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
                                | true =>
                                  exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
                        | true =>
                          cases h2 : s 2 with
                          | false =>
                            cases h4 : s 4 with
                            | false =>
                              exact color_witness_220 s h2 h4 h12
                            | true =>
                              cases h5 : s 5 with
                              | false =>
                                exact color_witness_217 s h0 h2 h5 h12
                              | true =>
                                cases h6 : s 6 with
                                | false =>
                                  exact color_witness_214 s h2 h6 h12
                                | true =>
                                  cases h13 : s 13 with
                                  | false =>
                                    cases h18 : s 18 with
                                    | false =>
                                      exact color_witness_32 s h2 h12 h13 h18
                                    | true =>
                                      exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
                                  | true =>
                                    exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              cases h4 : s 4 with
                              | false =>
                                exact color_witness_219 s h3 h4 h12
                              | true =>
                                cases h5 : s 5 with
                                | false =>
                                  exact color_witness_216 s h3 h5 h12
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_213 s h0 h3 h6 h12
                                  | true =>
                                    cases h13 : s 13 with
                                    | false =>
                                      cases h18 : s 18 with
                                      | false =>
                                        exact color_witness_34 s h0 h12 h13 h18
                                      | true =>
                                        exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
                                    | true =>
                                      exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_34 s h0 h12 h13 h18
                                | true =>
                                  exact core_witness_10 s h1 h2 h3 h8 h9 h10 h14 h15 h16 h17 h18
                              | true =>
                                exact core_witness_9 s h1 h2 h3 h7 h8 h10 h11 h13 h14 h15 h16
              | true =>
                cases h1 : s 1 with
                | false =>
                  cases h5 : s 5 with
                  | false =>
                    exact color_witness_218 s h1 h5 h12
                  | true =>
                    cases h2 : s 2 with
                    | false =>
                      cases h4 : s 4 with
                      | false =>
                        exact color_witness_220 s h2 h4 h12
                      | true =>
                        cases h14 : s 14 with
                        | false =>
                          exact color_witness_154 s h1 h2 h12 h14
                        | true =>
                          cases h6 : s 6 with
                          | false =>
                            exact color_witness_214 s h2 h6 h12
                          | true =>
                            cases h10 : s 10 with
                            | false =>
                              exact color_witness_200 s h2 h10 h12
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_123 s h2 h12 h15
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_98 s h1 h12 h16
                                | true =>
                                  cases h13 : s 13 with
                                  | false =>
                                    cases h18 : s 18 with
                                    | false =>
                                      exact color_witness_32 s h2 h12 h13 h18
                                    | true =>
                                      exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
                                  | true =>
                                    exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
                    | true =>
                      cases h10 : s 10 with
                      | false =>
                        exact color_witness_201 s h1 h10 h12
                      | true =>
                        cases h6 : s 6 with
                        | false =>
                          exact color_witness_215 s h1 h6 h12
                        | true =>
                          cases h16 : s 16 with
                          | false =>
                            exact color_witness_98 s h1 h12 h16
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              cases h4 : s 4 with
                              | false =>
                                exact color_witness_219 s h3 h4 h12
                              | true =>
                                cases h14 : s 14 with
                                | false =>
                                  exact color_witness_153 s h3 h12 h14
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_122 s h1 h3 h12 h15
                                  | true =>
                                    cases h13 : s 13 with
                                    | false =>
                                      cases h18 : s 18 with
                                      | false =>
                                        exact color_witness_33 s h1 h12 h13 h18
                                      | true =>
                                        exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
                                    | true =>
                                      exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_33 s h1 h12 h13 h18
                                | true =>
                                  exact core_witness_7 s h0 h2 h3 h5 h6 h8 h9 h10 h16 h17 h18
                              | true =>
                                exact core_witness_6 s h0 h2 h3 h5 h6 h7 h8 h10 h11 h13 h16
                | true =>
                  cases h4 : s 4 with
                  | false =>
                    cases h2 : s 2 with
                    | false =>
                      exact color_witness_220 s h2 h4 h12
                    | true =>
                      cases h5 : s 5 with
                      | false =>
                        cases h14 : s 14 with
                        | false =>
                          exact color_witness_152 s h4 h5 h12 h14
                        | true =>
                          cases h3 : s 3 with
                          | false =>
                            exact color_witness_216 s h3 h5 h12
                          | true =>
                            cases h10 : s 10 with
                            | false =>
                              exact color_witness_198 s h5 h10 h12
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_121 s h5 h12 h15
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_96 s h4 h12 h16
                                | true =>
                                  cases h13 : s 13 with
                                  | false =>
                                    cases h18 : s 18 with
                                    | false =>
                                      exact color_witness_30 s h5 h12 h13 h18
                                    | true =>
                                      exact core_witness_10 s h1 h2 h3 h8 h9 h10 h14 h15 h16 h17 h18
                                  | true =>
                                    exact core_witness_9 s h1 h2 h3 h7 h8 h10 h11 h13 h14 h15 h16
                      | true =>
                        cases h14 : s 14 with
                        | false =>
                          cases h3 : s 3 with
                          | false =>
                            exact color_witness_153 s h3 h12 h14
                          | true =>
                            cases h10 : s 10 with
                            | false =>
                              exact color_witness_148 s h10 h12 h14
                            | true =>
                              cases h6 : s 6 with
                              | false =>
                                exact color_witness_151 s h6 h12 h14
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_96 s h4 h12 h16
                                | true =>
                                  cases h13 : s 13 with
                                  | false =>
                                    cases h18 : s 18 with
                                    | false =>
                                      exact color_witness_25 s h12 h13 h14 h18
                                    | true =>
                                      exact core_witness_7 s h0 h2 h3 h5 h6 h8 h9 h10 h16 h17 h18
                                  | true =>
                                    exact core_witness_6 s h0 h2 h3 h5 h6 h7 h8 h10 h11 h13 h16
                        | true =>
                          cases h3 : s 3 with
                          | false =>
                            exact color_witness_219 s h3 h4 h12
                          | true =>
                            cases h10 : s 10 with
                            | false =>
                              exact color_witness_199 s h4 h10 h12
                            | true =>
                              cases h16 : s 16 with
                              | false =>
                                exact color_witness_96 s h4 h12 h16
                              | true =>
                                cases h6 : s 6 with
                                | false =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_120 s h4 h6 h12 h15
                                  | true =>
                                    cases h13 : s 13 with
                                    | false =>
                                      cases h18 : s 18 with
                                      | false =>
                                        exact color_witness_31 s h4 h12 h13 h18
                                      | true =>
                                        exact core_witness_10 s h1 h2 h3 h8 h9 h10 h14 h15 h16 h17 h18
                                    | true =>
                                      exact core_witness_9 s h1 h2 h3 h7 h8 h10 h11 h13 h14 h15 h16
                                | true =>
                                  cases h13 : s 13 with
                                  | false =>
                                    cases h18 : s 18 with
                                    | false =>
                                      exact color_witness_31 s h4 h12 h13 h18
                                    | true =>
                                      exact core_witness_7 s h0 h2 h3 h5 h6 h8 h9 h10 h16 h17 h18
                                  | true =>
                                    exact core_witness_6 s h0 h2 h3 h5 h6 h7 h8 h10 h11 h13 h16
                  | true =>
                    cases h2 : s 2 with
                    | false =>
                      cases h10 : s 10 with
                      | false =>
                        exact color_witness_200 s h2 h10 h12
                      | true =>
                        cases h6 : s 6 with
                        | false =>
                          exact color_witness_214 s h2 h6 h12
                        | true =>
                          cases h15 : s 15 with
                          | false =>
                            exact color_witness_123 s h2 h12 h15
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              cases h5 : s 5 with
                              | false =>
                                exact color_witness_216 s h3 h5 h12
                              | true =>
                                cases h14 : s 14 with
                                | false =>
                                  exact color_witness_153 s h3 h12 h14
                                | true =>
                                  cases h16 : s 16 with
                                  | false =>
                                    exact color_witness_97 s h2 h3 h12 h16
                                  | true =>
                                    cases h13 : s 13 with
                                    | false =>
                                      cases h18 : s 18 with
                                      | false =>
                                        exact color_witness_32 s h2 h12 h13 h18
                                      | true =>
                                        exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
                                    | true =>
                                      exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_32 s h2 h12 h13 h18
                                | true =>
                                  exact core_witness_4 s h0 h1 h3 h4 h6 h8 h9 h10 h15 h17 h18
                              | true =>
                                exact core_witness_3 s h0 h1 h3 h4 h6 h7 h8 h10 h11 h13 h15
                    | true =>
                      cases h5 : s 5 with
                      | false =>
                        cases h14 : s 14 with
                        | false =>
                          cases h3 : s 3 with
                          | false =>
                            exact color_witness_153 s h3 h12 h14
                          | true =>
                            cases h10 : s 10 with
                            | false =>
                              exact color_witness_148 s h10 h12 h14
                            | true =>
                              cases h6 : s 6 with
                              | false =>
                                exact color_witness_151 s h6 h12 h14
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  exact color_witness_121 s h5 h12 h15
                                | true =>
                                  cases h13 : s 13 with
                                  | false =>
                                    cases h18 : s 18 with
                                    | false =>
                                      exact color_witness_25 s h12 h13 h14 h18
                                    | true =>
                                      exact core_witness_4 s h0 h1 h3 h4 h6 h8 h9 h10 h15 h17 h18
                                  | true =>
                                    exact core_witness_3 s h0 h1 h3 h4 h6 h7 h8 h10 h11 h13 h15
                        | true =>
                          cases h3 : s 3 with
                          | false =>
                            exact color_witness_216 s h3 h5 h12
                          | true =>
                            cases h10 : s 10 with
                            | false =>
                              exact color_witness_198 s h5 h10 h12
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_121 s h5 h12 h15
                              | true =>
                                cases h6 : s 6 with
                                | false =>
                                  cases h16 : s 16 with
                                  | false =>
                                    exact color_witness_95 s h5 h6 h12 h16
                                  | true =>
                                    cases h13 : s 13 with
                                    | false =>
                                      cases h18 : s 18 with
                                      | false =>
                                        exact color_witness_30 s h5 h12 h13 h18
                                      | true =>
                                        exact core_witness_10 s h1 h2 h3 h8 h9 h10 h14 h15 h16 h17 h18
                                    | true =>
                                      exact core_witness_9 s h1 h2 h3 h7 h8 h10 h11 h13 h14 h15 h16
                                | true =>
                                  cases h13 : s 13 with
                                  | false =>
                                    cases h18 : s 18 with
                                    | false =>
                                      exact color_witness_30 s h5 h12 h13 h18
                                    | true =>
                                      exact core_witness_4 s h0 h1 h3 h4 h6 h8 h9 h10 h15 h17 h18
                                  | true =>
                                    exact core_witness_3 s h0 h1 h3 h4 h6 h7 h8 h10 h11 h13 h15
                      | true =>
                        cases h14 : s 14 with
                        | false =>
                          cases h3 : s 3 with
                          | false =>
                            exact color_witness_153 s h3 h12 h14
                          | true =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_151 s h6 h12 h14
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_148 s h10 h12 h14
                              | true =>
                                cases h13 : s 13 with
                                | false =>
                                  cases h18 : s 18 with
                                  | false =>
                                    exact color_witness_25 s h12 h13 h14 h18
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_86 s h12 h14 h15 h16
                                      | true =>
                                        exact core_witness_7 s h0 h2 h3 h5 h6 h8 h9 h10 h16 h17 h18
                                    | true =>
                                      exact core_witness_4 s h0 h1 h3 h4 h6 h8 h9 h10 h15 h17 h18
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_86 s h12 h14 h15 h16
                                    | true =>
                                      exact core_witness_6 s h0 h2 h3 h5 h6 h7 h8 h10 h11 h13 h16
                                  | true =>
                                    exact core_witness_3 s h0 h1 h3 h4 h6 h7 h8 h10 h11 h13 h15
                        | true =>
                          exact core_witness_0 s h0 h1 h2 h4 h5 h14
      | true =>
        cases h8 : s 8 with
        | false =>
          cases h10 : s 10 with
          | false =>
            cases h11 : s 11 with
            | false =>
              cases h13 : s 13 with
              | false =>
                cases h0 : s 0 with
                | false =>
                  exact color_witness_197 s h0 h8 h13
                | true =>
                  cases h1 : s 1 with
                  | false =>
                    exact color_witness_196 s h1 h8 h13
                  | true =>
                    cases h4 : s 4 with
                    | false =>
                      exact color_witness_194 s h4 h8 h13
                    | true =>
                      cases h2 : s 2 with
                      | false =>
                        exact color_witness_195 s h2 h8 h13
                      | true =>
                        cases h5 : s 5 with
                        | false =>
                          exact color_witness_193 s h5 h8 h13
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            exact color_witness_147 s h8 h13 h14
                          | true =>
                            exact core_witness_0 s h0 h1 h2 h4 h5 h14
              | true =>
                cases h18 : s 18 with
                | false =>
                  cases h17 : s 17 with
                  | false =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_39 s h0 h11 h18
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_38 s h1 h11 h18
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_36 s h4 h11 h18
                        | true =>
                          cases h2 : s 2 with
                          | false =>
                            exact color_witness_37 s h2 h11 h18
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_35 s h5 h11 h18
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_26 s h11 h14 h18
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
                  | true =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_39 s h0 h11 h18
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_38 s h1 h11 h18
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_36 s h4 h11 h18
                        | true =>
                          cases h2 : s 2 with
                          | false =>
                            exact color_witness_37 s h2 h11 h18
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_35 s h5 h11 h18
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_26 s h11 h14 h18
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
                | true =>
                  cases h0 : s 0 with
                  | false =>
                    exact color_witness_226 s h0 h10 h11
                  | true =>
                    cases h1 : s 1 with
                    | false =>
                      exact color_witness_225 s h1 h10 h11
                    | true =>
                      cases h4 : s 4 with
                      | false =>
                        exact color_witness_223 s h4 h10 h11
                      | true =>
                        cases h2 : s 2 with
                        | false =>
                          exact color_witness_224 s h2 h10 h11
                        | true =>
                          cases h5 : s 5 with
                          | false =>
                            exact color_witness_222 s h5 h10 h11
                          | true =>
                            cases h14 : s 14 with
                            | false =>
                              exact color_witness_156 s h10 h11 h14
                            | true =>
                              exact core_witness_0 s h0 h1 h2 h4 h5 h14
            | true =>
              cases h17 : s 17 with
              | false =>
                cases h18 : s 18 with
                | false =>
                  cases h0 : s 0 with
                  | false =>
                    exact color_witness_49 s h0 h8 h18
                  | true =>
                    cases h1 : s 1 with
                    | false =>
                      exact color_witness_48 s h1 h8 h18
                    | true =>
                      cases h4 : s 4 with
                      | false =>
                        exact color_witness_46 s h4 h8 h18
                      | true =>
                        cases h2 : s 2 with
                        | false =>
                          exact color_witness_47 s h2 h8 h18
                        | true =>
                          cases h5 : s 5 with
                          | false =>
                            exact color_witness_45 s h5 h8 h18
                          | true =>
                            cases h14 : s 14 with
                            | false =>
                              exact color_witness_28 s h8 h14 h18
                            | true =>
                              exact core_witness_0 s h0 h1 h2 h4 h5 h14
                | true =>
                  cases h13 : s 13 with
                  | false =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_64 s h0 h13 h17
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_63 s h1 h13 h17
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_61 s h4 h13 h17
                        | true =>
                          cases h2 : s 2 with
                          | false =>
                            exact color_witness_62 s h2 h13 h17
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_60 s h5 h13 h17
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_55 s h13 h14 h17
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
                  | true =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_74 s h0 h10 h17
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_73 s h1 h10 h17
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_71 s h4 h10 h17
                        | true =>
                          cases h2 : s 2 with
                          | false =>
                            exact color_witness_72 s h2 h10 h17
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_70 s h5 h10 h17
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_57 s h10 h14 h17
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
              | true =>
                cases h0 : s 0 with
                | false =>
                  cases h14 : s 14 with
                  | false =>
                    exact color_witness_163 s h0 h8 h10 h14
                  | true =>
                    cases h1 : s 1 with
                    | false =>
                      cases h4 : s 4 with
                      | false =>
                        exact color_witness_245 s h0 h1 h4 h8 h10
                      | true =>
                        cases h5 : s 5 with
                        | false =>
                          exact color_witness_242 s h1 h5 h8 h10
                        | true =>
                          cases h13 : s 13 with
                          | false =>
                            exact color_witness_196 s h1 h8 h13
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_48 s h1 h8 h18
                            | true =>
                              cases h16 : s 16 with
                              | false =>
                                exact color_witness_103 s h1 h8 h10 h16
                              | true =>
                                cases h6 : s 6 with
                                | false =>
                                  exact color_witness_239 s h1 h6 h8 h10
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_129 s h0 h8 h10 h15
                                  | true =>
                                    exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
                    | true =>
                      cases h2 : s 2 with
                      | false =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_244 s h2 h4 h8 h10
                        | true =>
                          cases h5 : s 5 with
                          | false =>
                            exact color_witness_241 s h0 h2 h5 h8 h10
                          | true =>
                            cases h13 : s 13 with
                            | false =>
                              exact color_witness_195 s h2 h8 h13
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_128 s h2 h8 h10 h15
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_47 s h2 h8 h18
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_238 s h2 h6 h8 h10
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_104 s h0 h8 h10 h16
                                    | true =>
                                      exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          cases h13 : s 13 with
                          | false =>
                            exact color_witness_194 s h4 h8 h13
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_46 s h4 h8 h18
                            | true =>
                              cases h16 : s 16 with
                              | false =>
                                exact color_witness_101 s h4 h8 h10 h16
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  exact color_witness_243 s h3 h4 h8 h10
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_129 s h0 h8 h10 h15
                                  | true =>
                                    exact core_witness_11 s h1 h2 h3 h11 h12 h13 h14 h15 h16 h17 h18
                        | true =>
                          cases h5 : s 5 with
                          | false =>
                            cases h13 : s 13 with
                            | false =>
                              exact color_witness_193 s h5 h8 h13
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_126 s h5 h8 h10 h15
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_45 s h5 h8 h18
                                | true =>
                                  cases h3 : s 3 with
                                  | false =>
                                    exact color_witness_240 s h3 h5 h8 h10
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_104 s h0 h8 h10 h16
                                    | true =>
                                      exact core_witness_11 s h1 h2 h3 h11 h12 h13 h14 h15 h16 h17 h18
                          | true =>
                            cases h13 : s 13 with
                            | false =>
                              exact color_witness_197 s h0 h8 h13
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_129 s h0 h8 h10 h15
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_104 s h0 h8 h10 h16
                                | true =>
                                  cases h18 : s 18 with
                                  | false =>
                                    exact color_witness_49 s h0 h8 h18
                                  | true =>
                                    cases h3 : s 3 with
                                    | false =>
                                      cases h6 : s 6 with
                                      | false =>
                                        exact color_witness_237 s h0 h3 h6 h8 h10
                                      | true =>
                                        exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
                                    | true =>
                                      exact core_witness_11 s h1 h2 h3 h11 h12 h13 h14 h15 h16 h17 h18
                | true =>
                  cases h1 : s 1 with
                  | false =>
                    cases h5 : s 5 with
                    | false =>
                      exact color_witness_242 s h1 h5 h8 h10
                    | true =>
                      cases h2 : s 2 with
                      | false =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_244 s h2 h4 h8 h10
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            exact color_witness_162 s h1 h2 h8 h10 h14
                          | true =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_238 s h2 h6 h8 h10
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                exact color_witness_195 s h2 h8 h13
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_47 s h2 h8 h18
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_128 s h2 h8 h10 h15
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_103 s h1 h8 h10 h16
                                    | true =>
                                      exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          cases h13 : s 13 with
                          | false =>
                            exact color_witness_194 s h4 h8 h13
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_46 s h4 h8 h18
                            | true =>
                              cases h16 : s 16 with
                              | false =>
                                exact color_witness_101 s h4 h8 h10 h16
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  exact color_witness_243 s h3 h4 h8 h10
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_239 s h1 h6 h8 h10
                                  | true =>
                                    exact core_witness_8 s h0 h2 h3 h5 h6 h11 h12 h13 h16 h17 h18
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_159 s h6 h8 h10 h14
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                exact color_witness_147 s h8 h13 h14
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_28 s h8 h14 h18
                                | true =>
                                  cases h3 : s 3 with
                                  | false =>
                                    exact color_witness_161 s h3 h8 h10 h14
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_103 s h1 h8 h10 h16
                                    | true =>
                                      exact core_witness_8 s h0 h2 h3 h5 h6 h11 h12 h13 h16 h17 h18
                          | true =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_239 s h1 h6 h8 h10
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                exact color_witness_196 s h1 h8 h13
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_103 s h1 h8 h10 h16
                                | true =>
                                  cases h18 : s 18 with
                                  | false =>
                                    exact color_witness_48 s h1 h8 h18
                                  | true =>
                                    cases h3 : s 3 with
                                    | false =>
                                      cases h15 : s 15 with
                                      | false =>
                                        exact color_witness_127 s h1 h3 h8 h10 h15
                                      | true =>
                                        exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
                                    | true =>
                                      exact core_witness_8 s h0 h2 h3 h5 h6 h11 h12 h13 h16 h17 h18
                  | true =>
                    cases h4 : s 4 with
                    | false =>
                      cases h2 : s 2 with
                      | false =>
                        exact color_witness_244 s h2 h4 h8 h10
                      | true =>
                        cases h5 : s 5 with
                        | false =>
                          cases h14 : s 14 with
                          | false =>
                            exact color_witness_160 s h4 h5 h8 h10 h14
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_240 s h3 h5 h8 h10
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                exact color_witness_193 s h5 h8 h13
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_45 s h5 h8 h18
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_126 s h5 h8 h10 h15
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_101 s h4 h8 h10 h16
                                    | true =>
                                      exact core_witness_11 s h1 h2 h3 h11 h12 h13 h14 h15 h16 h17 h18
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_161 s h3 h8 h10 h14
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                exact color_witness_147 s h8 h13 h14
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_28 s h8 h14 h18
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_159 s h6 h8 h10 h14
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_101 s h4 h8 h10 h16
                                    | true =>
                                      exact core_witness_8 s h0 h2 h3 h5 h6 h11 h12 h13 h16 h17 h18
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_243 s h3 h4 h8 h10
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                exact color_witness_194 s h4 h8 h13
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_101 s h4 h8 h10 h16
                                | true =>
                                  cases h18 : s 18 with
                                  | false =>
                                    exact color_witness_46 s h4 h8 h18
                                  | true =>
                                    cases h6 : s 6 with
                                    | false =>
                                      cases h15 : s 15 with
                                      | false =>
                                        exact color_witness_125 s h4 h6 h8 h10 h15
                                      | true =>
                                        exact core_witness_11 s h1 h2 h3 h11 h12 h13 h14 h15 h16 h17 h18
                                    | true =>
                                      exact core_witness_8 s h0 h2 h3 h5 h6 h11 h12 h13 h16 h17 h18
                    | true =>
                      cases h2 : s 2 with
                      | false =>
                        cases h5 : s 5 with
                        | false =>
                          cases h13 : s 13 with
                          | false =>
                            exact color_witness_193 s h5 h8 h13
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_45 s h5 h8 h18
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_126 s h5 h8 h10 h15
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  exact color_witness_240 s h3 h5 h8 h10
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_238 s h2 h6 h8 h10
                                  | true =>
                                    exact core_witness_5 s h0 h1 h3 h4 h6 h11 h12 h13 h15 h17 h18
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_159 s h6 h8 h10 h14
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                exact color_witness_147 s h8 h13 h14
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_28 s h8 h14 h18
                                | true =>
                                  cases h3 : s 3 with
                                  | false =>
                                    exact color_witness_161 s h3 h8 h10 h14
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      exact color_witness_128 s h2 h8 h10 h15
                                    | true =>
                                      exact core_witness_5 s h0 h1 h3 h4 h6 h11 h12 h13 h15 h17 h18
                          | true =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_238 s h2 h6 h8 h10
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                exact color_witness_195 s h2 h8 h13
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  exact color_witness_128 s h2 h8 h10 h15
                                | true =>
                                  cases h18 : s 18 with
                                  | false =>
                                    exact color_witness_47 s h2 h8 h18
                                  | true =>
                                    cases h3 : s 3 with
                                    | false =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_102 s h2 h3 h8 h10 h16
                                      | true =>
                                        exact core_witness_14 s h4 h5 h6 h11 h12 h13 h14 h15 h16 h17 h18
                                    | true =>
                                      exact core_witness_5 s h0 h1 h3 h4 h6 h11 h12 h13 h15 h17 h18
                      | true =>
                        cases h5 : s 5 with
                        | false =>
                          cases h14 : s 14 with
                          | false =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_161 s h3 h8 h10 h14
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                exact color_witness_147 s h8 h13 h14
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_28 s h8 h14 h18
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_159 s h6 h8 h10 h14
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      exact color_witness_126 s h5 h8 h10 h15
                                    | true =>
                                      exact core_witness_5 s h0 h1 h3 h4 h6 h11 h12 h13 h15 h17 h18
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_240 s h3 h5 h8 h10
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                exact color_witness_193 s h5 h8 h13
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  exact color_witness_126 s h5 h8 h10 h15
                                | true =>
                                  cases h18 : s 18 with
                                  | false =>
                                    exact color_witness_45 s h5 h8 h18
                                  | true =>
                                    cases h6 : s 6 with
                                    | false =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_100 s h5 h6 h8 h10 h16
                                      | true =>
                                        exact core_witness_11 s h1 h2 h3 h11 h12 h13 h14 h15 h16 h17 h18
                                    | true =>
                                      exact core_witness_5 s h0 h1 h3 h4 h6 h11 h12 h13 h15 h17 h18
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_161 s h3 h8 h10 h14
                            | true =>
                              cases h6 : s 6 with
                              | false =>
                                exact color_witness_159 s h6 h8 h10 h14
                              | true =>
                                cases h13 : s 13 with
                                | false =>
                                  exact color_witness_147 s h8 h13 h14
                                | true =>
                                  cases h18 : s 18 with
                                  | false =>
                                    exact color_witness_28 s h8 h14 h18
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_87 s h8 h10 h14 h15 h16
                                      | true =>
                                        exact core_witness_8 s h0 h2 h3 h5 h6 h11 h12 h13 h16 h17 h18
                                    | true =>
                                      exact core_witness_5 s h0 h1 h3 h4 h6 h11 h12 h13 h15 h17 h18
                          | true =>
                            exact core_witness_0 s h0 h1 h2 h4 h5 h14
          | true =>
            cases h13 : s 13 with
            | false =>
              cases h18 : s 18 with
              | false =>
                cases h11 : s 11 with
                | false =>
                  cases h17 : s 17 with
                  | false =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_39 s h0 h11 h18
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_38 s h1 h11 h18
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_36 s h4 h11 h18
                        | true =>
                          cases h2 : s 2 with
                          | false =>
                            exact color_witness_37 s h2 h11 h18
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_35 s h5 h11 h18
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_26 s h11 h14 h18
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
                  | true =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_39 s h0 h11 h18
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_38 s h1 h11 h18
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_36 s h4 h11 h18
                        | true =>
                          cases h2 : s 2 with
                          | false =>
                            exact color_witness_37 s h2 h11 h18
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_35 s h5 h11 h18
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_26 s h11 h14 h18
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
                | true =>
                  cases h17 : s 17 with
                  | false =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_49 s h0 h8 h18
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_48 s h1 h8 h18
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_46 s h4 h8 h18
                        | true =>
                          cases h2 : s 2 with
                          | false =>
                            exact color_witness_47 s h2 h8 h18
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_45 s h5 h8 h18
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_28 s h8 h14 h18
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
                  | true =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_49 s h0 h8 h18
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_48 s h1 h8 h18
                      | true =>
                        cases h2 : s 2 with
                        | false =>
                          exact color_witness_47 s h2 h8 h18
                        | true =>
                          cases h4 : s 4 with
                          | false =>
                            exact color_witness_46 s h4 h8 h18
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_45 s h5 h8 h18
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_28 s h8 h14 h18
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
              | true =>
                cases h11 : s 11 with
                | false =>
                  cases h0 : s 0 with
                  | false =>
                    exact color_witness_197 s h0 h8 h13
                  | true =>
                    cases h1 : s 1 with
                    | false =>
                      exact color_witness_196 s h1 h8 h13
                    | true =>
                      cases h4 : s 4 with
                      | false =>
                        exact color_witness_194 s h4 h8 h13
                      | true =>
                        cases h2 : s 2 with
                        | false =>
                          exact color_witness_195 s h2 h8 h13
                        | true =>
                          cases h5 : s 5 with
                          | false =>
                            exact color_witness_193 s h5 h8 h13
                          | true =>
                            cases h14 : s 14 with
                            | false =>
                              exact color_witness_147 s h8 h13 h14
                            | true =>
                              exact core_witness_0 s h0 h1 h2 h4 h5 h14
                | true =>
                  cases h17 : s 17 with
                  | false =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_64 s h0 h13 h17
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_63 s h1 h13 h17
                      | true =>
                        cases h2 : s 2 with
                        | false =>
                          exact color_witness_62 s h2 h13 h17
                        | true =>
                          cases h4 : s 4 with
                          | false =>
                            exact color_witness_61 s h4 h13 h17
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_60 s h5 h13 h17
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_55 s h13 h14 h17
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
                  | true =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_197 s h0 h8 h13
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_196 s h1 h8 h13
                      | true =>
                        cases h2 : s 2 with
                        | false =>
                          exact color_witness_195 s h2 h8 h13
                        | true =>
                          cases h4 : s 4 with
                          | false =>
                            exact color_witness_194 s h4 h8 h13
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_193 s h5 h8 h13
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_147 s h8 h13 h14
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
            | true =>
              cases h18 : s 18 with
              | false =>
                cases h17 : s 17 with
                | false =>
                  cases h0 : s 0 with
                  | false =>
                    exact color_witness_49 s h0 h8 h18
                  | true =>
                    cases h1 : s 1 with
                    | false =>
                      exact color_witness_48 s h1 h8 h18
                    | true =>
                      cases h4 : s 4 with
                      | false =>
                        exact color_witness_46 s h4 h8 h18
                      | true =>
                        cases h2 : s 2 with
                        | false =>
                          exact color_witness_47 s h2 h8 h18
                        | true =>
                          cases h5 : s 5 with
                          | false =>
                            exact color_witness_45 s h5 h8 h18
                          | true =>
                            cases h14 : s 14 with
                            | false =>
                              exact color_witness_28 s h8 h14 h18
                            | true =>
                              exact core_witness_0 s h0 h1 h2 h4 h5 h14
                | true =>
                  cases h11 : s 11 with
                  | false =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_39 s h0 h11 h18
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_38 s h1 h11 h18
                      | true =>
                        cases h2 : s 2 with
                        | false =>
                          exact color_witness_37 s h2 h11 h18
                        | true =>
                          cases h4 : s 4 with
                          | false =>
                            exact color_witness_36 s h4 h11 h18
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_35 s h5 h11 h18
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_26 s h11 h14 h18
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
                  | true =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_49 s h0 h8 h18
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_48 s h1 h8 h18
                      | true =>
                        cases h2 : s 2 with
                        | false =>
                          exact color_witness_47 s h2 h8 h18
                        | true =>
                          cases h4 : s 4 with
                          | false =>
                            exact color_witness_46 s h4 h8 h18
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_45 s h5 h8 h18
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_28 s h8 h14 h18
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
              | true =>
                exact core_witness_2 s h7 h9 h10 h12 h13 h18
        | true =>
          cases h11 : s 11 with
          | false =>
            cases h13 : s 13 with
            | false =>
              cases h17 : s 17 with
              | false =>
                cases h18 : s 18 with
                | false =>
                  cases h0 : s 0 with
                  | false =>
                    exact color_witness_39 s h0 h11 h18
                  | true =>
                    cases h1 : s 1 with
                    | false =>
                      exact color_witness_38 s h1 h11 h18
                    | true =>
                      cases h4 : s 4 with
                      | false =>
                        exact color_witness_36 s h4 h11 h18
                      | true =>
                        cases h2 : s 2 with
                        | false =>
                          exact color_witness_37 s h2 h11 h18
                        | true =>
                          cases h5 : s 5 with
                          | false =>
                            exact color_witness_35 s h5 h11 h18
                          | true =>
                            cases h14 : s 14 with
                            | false =>
                              exact color_witness_26 s h11 h14 h18
                            | true =>
                              exact core_witness_0 s h0 h1 h2 h4 h5 h14
                | true =>
                  cases h10 : s 10 with
                  | false =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_64 s h0 h13 h17
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_63 s h1 h13 h17
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_61 s h4 h13 h17
                        | true =>
                          cases h2 : s 2 with
                          | false =>
                            exact color_witness_62 s h2 h13 h17
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_60 s h5 h13 h17
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_55 s h13 h14 h17
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
                  | true =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_64 s h0 h13 h17
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_63 s h1 h13 h17
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_61 s h4 h13 h17
                        | true =>
                          cases h2 : s 2 with
                          | false =>
                            exact color_witness_62 s h2 h13 h17
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_60 s h5 h13 h17
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_55 s h13 h14 h17
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
              | true =>
                cases h0 : s 0 with
                | false =>
                  cases h14 : s 14 with
                  | false =>
                    exact color_witness_144 s h0 h11 h13 h14
                  | true =>
                    cases h1 : s 1 with
                    | false =>
                      cases h4 : s 4 with
                      | false =>
                        exact color_witness_182 s h0 h1 h4 h11 h13
                      | true =>
                        cases h5 : s 5 with
                        | false =>
                          exact color_witness_179 s h1 h5 h11 h13
                        | true =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_225 s h1 h10 h11
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_38 s h1 h11 h18
                            | true =>
                              cases h16 : s 16 with
                              | false =>
                                exact color_witness_93 s h1 h11 h13 h16
                              | true =>
                                cases h6 : s 6 with
                                | false =>
                                  exact color_witness_176 s h1 h6 h11 h13
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_119 s h0 h11 h13 h15
                                  | true =>
                                    exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
                    | true =>
                      cases h2 : s 2 with
                      | false =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_181 s h2 h4 h11 h13
                        | true =>
                          cases h5 : s 5 with
                          | false =>
                            exact color_witness_178 s h0 h2 h5 h11 h13
                          | true =>
                            cases h10 : s 10 with
                            | false =>
                              exact color_witness_224 s h2 h10 h11
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_118 s h2 h11 h13 h15
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_37 s h2 h11 h18
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_175 s h2 h6 h11 h13
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_94 s h0 h11 h13 h16
                                    | true =>
                                      exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_223 s h4 h10 h11
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_36 s h4 h11 h18
                            | true =>
                              cases h16 : s 16 with
                              | false =>
                                exact color_witness_91 s h4 h11 h13 h16
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  exact color_witness_180 s h3 h4 h11 h13
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_119 s h0 h11 h13 h15
                                  | true =>
                                    exact core_witness_10 s h1 h2 h3 h8 h9 h10 h14 h15 h16 h17 h18
                        | true =>
                          cases h5 : s 5 with
                          | false =>
                            cases h10 : s 10 with
                            | false =>
                              exact color_witness_222 s h5 h10 h11
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_116 s h5 h11 h13 h15
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_35 s h5 h11 h18
                                | true =>
                                  cases h3 : s 3 with
                                  | false =>
                                    exact color_witness_177 s h3 h5 h11 h13
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_94 s h0 h11 h13 h16
                                    | true =>
                                      exact core_witness_10 s h1 h2 h3 h8 h9 h10 h14 h15 h16 h17 h18
                          | true =>
                            cases h10 : s 10 with
                            | false =>
                              exact color_witness_226 s h0 h10 h11
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_119 s h0 h11 h13 h15
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_94 s h0 h11 h13 h16
                                | true =>
                                  cases h18 : s 18 with
                                  | false =>
                                    exact color_witness_39 s h0 h11 h18
                                  | true =>
                                    cases h3 : s 3 with
                                    | false =>
                                      cases h6 : s 6 with
                                      | false =>
                                        exact color_witness_174 s h0 h3 h6 h11 h13
                                      | true =>
                                        exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
                                    | true =>
                                      exact core_witness_10 s h1 h2 h3 h8 h9 h10 h14 h15 h16 h17 h18
                | true =>
                  cases h1 : s 1 with
                  | false =>
                    cases h5 : s 5 with
                    | false =>
                      exact color_witness_179 s h1 h5 h11 h13
                    | true =>
                      cases h2 : s 2 with
                      | false =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_181 s h2 h4 h11 h13
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            exact color_witness_143 s h1 h2 h11 h13 h14
                          | true =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_175 s h2 h6 h11 h13
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_224 s h2 h10 h11
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_37 s h2 h11 h18
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_118 s h2 h11 h13 h15
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_93 s h1 h11 h13 h16
                                    | true =>
                                      exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_223 s h4 h10 h11
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_36 s h4 h11 h18
                            | true =>
                              cases h16 : s 16 with
                              | false =>
                                exact color_witness_91 s h4 h11 h13 h16
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  exact color_witness_180 s h3 h4 h11 h13
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_176 s h1 h6 h11 h13
                                  | true =>
                                    exact core_witness_7 s h0 h2 h3 h5 h6 h8 h9 h10 h16 h17 h18
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_140 s h6 h11 h13 h14
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_156 s h10 h11 h14
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_26 s h11 h14 h18
                                | true =>
                                  cases h3 : s 3 with
                                  | false =>
                                    exact color_witness_142 s h3 h11 h13 h14
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_93 s h1 h11 h13 h16
                                    | true =>
                                      exact core_witness_7 s h0 h2 h3 h5 h6 h8 h9 h10 h16 h17 h18
                          | true =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_176 s h1 h6 h11 h13
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_225 s h1 h10 h11
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_93 s h1 h11 h13 h16
                                | true =>
                                  cases h18 : s 18 with
                                  | false =>
                                    exact color_witness_38 s h1 h11 h18
                                  | true =>
                                    cases h3 : s 3 with
                                    | false =>
                                      cases h15 : s 15 with
                                      | false =>
                                        exact color_witness_117 s h1 h3 h11 h13 h15
                                      | true =>
                                        exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
                                    | true =>
                                      exact core_witness_7 s h0 h2 h3 h5 h6 h8 h9 h10 h16 h17 h18
                  | true =>
                    cases h4 : s 4 with
                    | false =>
                      cases h2 : s 2 with
                      | false =>
                        exact color_witness_181 s h2 h4 h11 h13
                      | true =>
                        cases h5 : s 5 with
                        | false =>
                          cases h14 : s 14 with
                          | false =>
                            exact color_witness_141 s h4 h5 h11 h13 h14
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_177 s h3 h5 h11 h13
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_222 s h5 h10 h11
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_35 s h5 h11 h18
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_116 s h5 h11 h13 h15
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_91 s h4 h11 h13 h16
                                    | true =>
                                      exact core_witness_10 s h1 h2 h3 h8 h9 h10 h14 h15 h16 h17 h18
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_142 s h3 h11 h13 h14
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_156 s h10 h11 h14
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_26 s h11 h14 h18
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_140 s h6 h11 h13 h14
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_91 s h4 h11 h13 h16
                                    | true =>
                                      exact core_witness_7 s h0 h2 h3 h5 h6 h8 h9 h10 h16 h17 h18
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_180 s h3 h4 h11 h13
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_223 s h4 h10 h11
                              | true =>
                                cases h16 : s 16 with
                                | false =>
                                  exact color_witness_91 s h4 h11 h13 h16
                                | true =>
                                  cases h18 : s 18 with
                                  | false =>
                                    exact color_witness_36 s h4 h11 h18
                                  | true =>
                                    cases h6 : s 6 with
                                    | false =>
                                      cases h15 : s 15 with
                                      | false =>
                                        exact color_witness_115 s h4 h6 h11 h13 h15
                                      | true =>
                                        exact core_witness_10 s h1 h2 h3 h8 h9 h10 h14 h15 h16 h17 h18
                                    | true =>
                                      exact core_witness_7 s h0 h2 h3 h5 h6 h8 h9 h10 h16 h17 h18
                    | true =>
                      cases h2 : s 2 with
                      | false =>
                        cases h5 : s 5 with
                        | false =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_222 s h5 h10 h11
                          | true =>
                            cases h18 : s 18 with
                            | false =>
                              exact color_witness_35 s h5 h11 h18
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_116 s h5 h11 h13 h15
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  exact color_witness_177 s h3 h5 h11 h13
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_175 s h2 h6 h11 h13
                                  | true =>
                                    exact core_witness_4 s h0 h1 h3 h4 h6 h8 h9 h10 h15 h17 h18
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_140 s h6 h11 h13 h14
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_156 s h10 h11 h14
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_26 s h11 h14 h18
                                | true =>
                                  cases h3 : s 3 with
                                  | false =>
                                    exact color_witness_142 s h3 h11 h13 h14
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      exact color_witness_118 s h2 h11 h13 h15
                                    | true =>
                                      exact core_witness_4 s h0 h1 h3 h4 h6 h8 h9 h10 h15 h17 h18
                          | true =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_175 s h2 h6 h11 h13
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_224 s h2 h10 h11
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  exact color_witness_118 s h2 h11 h13 h15
                                | true =>
                                  cases h18 : s 18 with
                                  | false =>
                                    exact color_witness_37 s h2 h11 h18
                                  | true =>
                                    cases h3 : s 3 with
                                    | false =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_92 s h2 h3 h11 h13 h16
                                      | true =>
                                        exact core_witness_13 s h4 h5 h6 h8 h9 h10 h14 h15 h16 h17 h18
                                    | true =>
                                      exact core_witness_4 s h0 h1 h3 h4 h6 h8 h9 h10 h15 h17 h18
                      | true =>
                        cases h5 : s 5 with
                        | false =>
                          cases h14 : s 14 with
                          | false =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_142 s h3 h11 h13 h14
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_156 s h10 h11 h14
                              | true =>
                                cases h18 : s 18 with
                                | false =>
                                  exact color_witness_26 s h11 h14 h18
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_140 s h6 h11 h13 h14
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      exact color_witness_116 s h5 h11 h13 h15
                                    | true =>
                                      exact core_witness_4 s h0 h1 h3 h4 h6 h8 h9 h10 h15 h17 h18
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_177 s h3 h5 h11 h13
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_222 s h5 h10 h11
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  exact color_witness_116 s h5 h11 h13 h15
                                | true =>
                                  cases h18 : s 18 with
                                  | false =>
                                    exact color_witness_35 s h5 h11 h18
                                  | true =>
                                    cases h6 : s 6 with
                                    | false =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_90 s h5 h6 h11 h13 h16
                                      | true =>
                                        exact core_witness_10 s h1 h2 h3 h8 h9 h10 h14 h15 h16 h17 h18
                                    | true =>
                                      exact core_witness_4 s h0 h1 h3 h4 h6 h8 h9 h10 h15 h17 h18
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_142 s h3 h11 h13 h14
                            | true =>
                              cases h6 : s 6 with
                              | false =>
                                exact color_witness_140 s h6 h11 h13 h14
                              | true =>
                                cases h10 : s 10 with
                                | false =>
                                  exact color_witness_156 s h10 h11 h14
                                | true =>
                                  cases h18 : s 18 with
                                  | false =>
                                    exact color_witness_26 s h11 h14 h18
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_85 s h11 h13 h14 h15 h16
                                      | true =>
                                        exact core_witness_7 s h0 h2 h3 h5 h6 h8 h9 h10 h16 h17 h18
                                    | true =>
                                      exact core_witness_4 s h0 h1 h3 h4 h6 h8 h9 h10 h15 h17 h18
                          | true =>
                            exact core_witness_0 s h0 h1 h2 h4 h5 h14
            | true =>
              cases h18 : s 18 with
              | false =>
                cases h17 : s 17 with
                | false =>
                  cases h10 : s 10 with
                  | false =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_39 s h0 h11 h18
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_38 s h1 h11 h18
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_36 s h4 h11 h18
                        | true =>
                          cases h2 : s 2 with
                          | false =>
                            exact color_witness_37 s h2 h11 h18
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_35 s h5 h11 h18
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_26 s h11 h14 h18
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
                  | true =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_39 s h0 h11 h18
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_38 s h1 h11 h18
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_36 s h4 h11 h18
                        | true =>
                          cases h2 : s 2 with
                          | false =>
                            exact color_witness_37 s h2 h11 h18
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_35 s h5 h11 h18
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_26 s h11 h14 h18
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
                | true =>
                  cases h10 : s 10 with
                  | false =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_39 s h0 h11 h18
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_38 s h1 h11 h18
                      | true =>
                        cases h2 : s 2 with
                        | false =>
                          exact color_witness_37 s h2 h11 h18
                        | true =>
                          cases h4 : s 4 with
                          | false =>
                            exact color_witness_36 s h4 h11 h18
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_35 s h5 h11 h18
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_26 s h11 h14 h18
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
                  | true =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_39 s h0 h11 h18
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_38 s h1 h11 h18
                      | true =>
                        cases h2 : s 2 with
                        | false =>
                          exact color_witness_37 s h2 h11 h18
                        | true =>
                          cases h4 : s 4 with
                          | false =>
                            exact color_witness_36 s h4 h11 h18
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_35 s h5 h11 h18
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_26 s h11 h14 h18
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
              | true =>
                cases h10 : s 10 with
                | false =>
                  cases h17 : s 17 with
                  | false =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_74 s h0 h10 h17
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_73 s h1 h10 h17
                      | true =>
                        cases h2 : s 2 with
                        | false =>
                          exact color_witness_72 s h2 h10 h17
                        | true =>
                          cases h4 : s 4 with
                          | false =>
                            exact color_witness_71 s h4 h10 h17
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_70 s h5 h10 h17
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_57 s h10 h14 h17
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
                  | true =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_226 s h0 h10 h11
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_225 s h1 h10 h11
                      | true =>
                        cases h2 : s 2 with
                        | false =>
                          exact color_witness_224 s h2 h10 h11
                        | true =>
                          cases h4 : s 4 with
                          | false =>
                            exact color_witness_223 s h4 h10 h11
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_222 s h5 h10 h11
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_156 s h10 h11 h14
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
                | true =>
                  exact core_witness_2 s h7 h9 h10 h12 h13 h18
          | true =>
            cases h17 : s 17 with
            | false =>
              cases h18 : s 18 with
              | false =>
                cases h0 : s 0 with
                | false =>
                  cases h14 : s 14 with
                  | false =>
                    exact color_witness_15 s h0 h14 h17 h18
                  | true =>
                    cases h1 : s 1 with
                    | false =>
                      cases h4 : s 4 with
                      | false =>
                        exact color_witness_24 s h0 h1 h4 h17 h18
                      | true =>
                        cases h5 : s 5 with
                        | false =>
                          exact color_witness_21 s h1 h5 h17 h18
                        | true =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_73 s h1 h10 h17
                          | true =>
                            cases h13 : s 13 with
                            | false =>
                              exact color_witness_63 s h1 h13 h17
                            | true =>
                              cases h16 : s 16 with
                              | false =>
                                exact color_witness_4 s h1 h16 h17 h18
                              | true =>
                                cases h6 : s 6 with
                                | false =>
                                  exact color_witness_18 s h1 h6 h17 h18
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_10 s h0 h15 h17 h18
                                  | true =>
                                    exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
                    | true =>
                      cases h2 : s 2 with
                      | false =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_23 s h2 h4 h17 h18
                        | true =>
                          cases h5 : s 5 with
                          | false =>
                            exact color_witness_20 s h0 h2 h5 h17 h18
                          | true =>
                            cases h10 : s 10 with
                            | false =>
                              exact color_witness_72 s h2 h10 h17
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                exact color_witness_62 s h2 h13 h17
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  exact color_witness_9 s h2 h15 h17 h18
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_17 s h2 h6 h17 h18
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_5 s h0 h16 h17 h18
                                    | true =>
                                      exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_71 s h4 h10 h17
                          | true =>
                            cases h13 : s 13 with
                            | false =>
                              exact color_witness_61 s h4 h13 h17
                            | true =>
                              cases h16 : s 16 with
                              | false =>
                                exact color_witness_2 s h4 h16 h17 h18
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  exact color_witness_22 s h3 h4 h17 h18
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_10 s h0 h15 h17 h18
                                  | true =>
                                    exact core_witness_9 s h1 h2 h3 h7 h8 h10 h11 h13 h14 h15 h16
                        | true =>
                          cases h5 : s 5 with
                          | false =>
                            cases h10 : s 10 with
                            | false =>
                              exact color_witness_70 s h5 h10 h17
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                exact color_witness_60 s h5 h13 h17
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  exact color_witness_7 s h5 h15 h17 h18
                                | true =>
                                  cases h3 : s 3 with
                                  | false =>
                                    exact color_witness_19 s h3 h5 h17 h18
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_5 s h0 h16 h17 h18
                                    | true =>
                                      exact core_witness_9 s h1 h2 h3 h7 h8 h10 h11 h13 h14 h15 h16
                          | true =>
                            cases h10 : s 10 with
                            | false =>
                              exact color_witness_74 s h0 h10 h17
                            | true =>
                              cases h13 : s 13 with
                              | false =>
                                exact color_witness_64 s h0 h13 h17
                              | true =>
                                cases h15 : s 15 with
                                | false =>
                                  exact color_witness_10 s h0 h15 h17 h18
                                | true =>
                                  cases h16 : s 16 with
                                  | false =>
                                    exact color_witness_5 s h0 h16 h17 h18
                                  | true =>
                                    cases h3 : s 3 with
                                    | false =>
                                      cases h6 : s 6 with
                                      | false =>
                                        exact color_witness_16 s h0 h3 h6 h17 h18
                                      | true =>
                                        exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
                                    | true =>
                                      exact core_witness_9 s h1 h2 h3 h7 h8 h10 h11 h13 h14 h15 h16
                | true =>
                  cases h1 : s 1 with
                  | false =>
                    cases h5 : s 5 with
                    | false =>
                      exact color_witness_21 s h1 h5 h17 h18
                    | true =>
                      cases h2 : s 2 with
                      | false =>
                        cases h4 : s 4 with
                        | false =>
                          exact color_witness_23 s h2 h4 h17 h18
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            exact color_witness_14 s h1 h2 h14 h17 h18
                          | true =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_17 s h2 h6 h17 h18
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_72 s h2 h10 h17
                              | true =>
                                cases h13 : s 13 with
                                | false =>
                                  exact color_witness_62 s h2 h13 h17
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_9 s h2 h15 h17 h18
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_4 s h1 h16 h17 h18
                                    | true =>
                                      exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
                      | true =>
                        cases h4 : s 4 with
                        | false =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_71 s h4 h10 h17
                          | true =>
                            cases h13 : s 13 with
                            | false =>
                              exact color_witness_61 s h4 h13 h17
                            | true =>
                              cases h16 : s 16 with
                              | false =>
                                exact color_witness_2 s h4 h16 h17 h18
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  exact color_witness_22 s h3 h4 h17 h18
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_18 s h1 h6 h17 h18
                                  | true =>
                                    exact core_witness_6 s h0 h2 h3 h5 h6 h7 h8 h10 h11 h13 h16
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_11 s h6 h14 h17 h18
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_57 s h10 h14 h17
                              | true =>
                                cases h13 : s 13 with
                                | false =>
                                  exact color_witness_55 s h13 h14 h17
                                | true =>
                                  cases h3 : s 3 with
                                  | false =>
                                    exact color_witness_13 s h3 h14 h17 h18
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_4 s h1 h16 h17 h18
                                    | true =>
                                      exact core_witness_6 s h0 h2 h3 h5 h6 h7 h8 h10 h11 h13 h16
                          | true =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_18 s h1 h6 h17 h18
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_73 s h1 h10 h17
                              | true =>
                                cases h13 : s 13 with
                                | false =>
                                  exact color_witness_63 s h1 h13 h17
                                | true =>
                                  cases h16 : s 16 with
                                  | false =>
                                    exact color_witness_4 s h1 h16 h17 h18
                                  | true =>
                                    cases h3 : s 3 with
                                    | false =>
                                      cases h15 : s 15 with
                                      | false =>
                                        exact color_witness_8 s h1 h3 h15 h17 h18
                                      | true =>
                                        exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
                                    | true =>
                                      exact core_witness_6 s h0 h2 h3 h5 h6 h7 h8 h10 h11 h13 h16
                  | true =>
                    cases h4 : s 4 with
                    | false =>
                      cases h2 : s 2 with
                      | false =>
                        exact color_witness_23 s h2 h4 h17 h18
                      | true =>
                        cases h5 : s 5 with
                        | false =>
                          cases h14 : s 14 with
                          | false =>
                            exact color_witness_12 s h4 h5 h14 h17 h18
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_19 s h3 h5 h17 h18
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_70 s h5 h10 h17
                              | true =>
                                cases h13 : s 13 with
                                | false =>
                                  exact color_witness_60 s h5 h13 h17
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_7 s h5 h15 h17 h18
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_2 s h4 h16 h17 h18
                                    | true =>
                                      exact core_witness_9 s h1 h2 h3 h7 h8 h10 h11 h13 h14 h15 h16
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_13 s h3 h14 h17 h18
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_57 s h10 h14 h17
                              | true =>
                                cases h13 : s 13 with
                                | false =>
                                  exact color_witness_55 s h13 h14 h17
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_11 s h6 h14 h17 h18
                                  | true =>
                                    cases h16 : s 16 with
                                    | false =>
                                      exact color_witness_2 s h4 h16 h17 h18
                                    | true =>
                                      exact core_witness_6 s h0 h2 h3 h5 h6 h7 h8 h10 h11 h13 h16
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_22 s h3 h4 h17 h18
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_71 s h4 h10 h17
                              | true =>
                                cases h13 : s 13 with
                                | false =>
                                  exact color_witness_61 s h4 h13 h17
                                | true =>
                                  cases h16 : s 16 with
                                  | false =>
                                    exact color_witness_2 s h4 h16 h17 h18
                                  | true =>
                                    cases h6 : s 6 with
                                    | false =>
                                      cases h15 : s 15 with
                                      | false =>
                                        exact color_witness_6 s h4 h6 h15 h17 h18
                                      | true =>
                                        exact core_witness_9 s h1 h2 h3 h7 h8 h10 h11 h13 h14 h15 h16
                                    | true =>
                                      exact core_witness_6 s h0 h2 h3 h5 h6 h7 h8 h10 h11 h13 h16
                    | true =>
                      cases h2 : s 2 with
                      | false =>
                        cases h5 : s 5 with
                        | false =>
                          cases h10 : s 10 with
                          | false =>
                            exact color_witness_70 s h5 h10 h17
                          | true =>
                            cases h13 : s 13 with
                            | false =>
                              exact color_witness_60 s h5 h13 h17
                            | true =>
                              cases h15 : s 15 with
                              | false =>
                                exact color_witness_7 s h5 h15 h17 h18
                              | true =>
                                cases h3 : s 3 with
                                | false =>
                                  exact color_witness_19 s h3 h5 h17 h18
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_17 s h2 h6 h17 h18
                                  | true =>
                                    exact core_witness_3 s h0 h1 h3 h4 h6 h7 h8 h10 h11 h13 h15
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_11 s h6 h14 h17 h18
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_57 s h10 h14 h17
                              | true =>
                                cases h13 : s 13 with
                                | false =>
                                  exact color_witness_55 s h13 h14 h17
                                | true =>
                                  cases h3 : s 3 with
                                  | false =>
                                    exact color_witness_13 s h3 h14 h17 h18
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      exact color_witness_9 s h2 h15 h17 h18
                                    | true =>
                                      exact core_witness_3 s h0 h1 h3 h4 h6 h7 h8 h10 h11 h13 h15
                          | true =>
                            cases h6 : s 6 with
                            | false =>
                              exact color_witness_17 s h2 h6 h17 h18
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_72 s h2 h10 h17
                              | true =>
                                cases h13 : s 13 with
                                | false =>
                                  exact color_witness_62 s h2 h13 h17
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_9 s h2 h15 h17 h18
                                  | true =>
                                    cases h3 : s 3 with
                                    | false =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_3 s h2 h3 h16 h17 h18
                                      | true =>
                                        exact core_witness_12 s h4 h5 h6 h7 h8 h10 h11 h13 h14 h15 h16
                                    | true =>
                                      exact core_witness_3 s h0 h1 h3 h4 h6 h7 h8 h10 h11 h13 h15
                      | true =>
                        cases h5 : s 5 with
                        | false =>
                          cases h14 : s 14 with
                          | false =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_13 s h3 h14 h17 h18
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_57 s h10 h14 h17
                              | true =>
                                cases h13 : s 13 with
                                | false =>
                                  exact color_witness_55 s h13 h14 h17
                                | true =>
                                  cases h6 : s 6 with
                                  | false =>
                                    exact color_witness_11 s h6 h14 h17 h18
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      exact color_witness_7 s h5 h15 h17 h18
                                    | true =>
                                      exact core_witness_3 s h0 h1 h3 h4 h6 h7 h8 h10 h11 h13 h15
                          | true =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_19 s h3 h5 h17 h18
                            | true =>
                              cases h10 : s 10 with
                              | false =>
                                exact color_witness_70 s h5 h10 h17
                              | true =>
                                cases h13 : s 13 with
                                | false =>
                                  exact color_witness_60 s h5 h13 h17
                                | true =>
                                  cases h15 : s 15 with
                                  | false =>
                                    exact color_witness_7 s h5 h15 h17 h18
                                  | true =>
                                    cases h6 : s 6 with
                                    | false =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_1 s h5 h6 h16 h17 h18
                                      | true =>
                                        exact core_witness_9 s h1 h2 h3 h7 h8 h10 h11 h13 h14 h15 h16
                                    | true =>
                                      exact core_witness_3 s h0 h1 h3 h4 h6 h7 h8 h10 h11 h13 h15
                        | true =>
                          cases h14 : s 14 with
                          | false =>
                            cases h3 : s 3 with
                            | false =>
                              exact color_witness_13 s h3 h14 h17 h18
                            | true =>
                              cases h6 : s 6 with
                              | false =>
                                exact color_witness_11 s h6 h14 h17 h18
                              | true =>
                                cases h10 : s 10 with
                                | false =>
                                  exact color_witness_57 s h10 h14 h17
                                | true =>
                                  cases h13 : s 13 with
                                  | false =>
                                    exact color_witness_55 s h13 h14 h17
                                  | true =>
                                    cases h15 : s 15 with
                                    | false =>
                                      cases h16 : s 16 with
                                      | false =>
                                        exact color_witness_0 s h14 h15 h16 h17 h18
                                      | true =>
                                        exact core_witness_6 s h0 h2 h3 h5 h6 h7 h8 h10 h11 h13 h16
                                    | true =>
                                      exact core_witness_3 s h0 h1 h3 h4 h6 h7 h8 h10 h11 h13 h15
                          | true =>
                            exact core_witness_0 s h0 h1 h2 h4 h5 h14
              | true =>
                cases h10 : s 10 with
                | false =>
                  cases h13 : s 13 with
                  | false =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_64 s h0 h13 h17
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_63 s h1 h13 h17
                      | true =>
                        cases h2 : s 2 with
                        | false =>
                          exact color_witness_62 s h2 h13 h17
                        | true =>
                          cases h4 : s 4 with
                          | false =>
                            exact color_witness_61 s h4 h13 h17
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_60 s h5 h13 h17
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_55 s h13 h14 h17
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
                  | true =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_74 s h0 h10 h17
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_73 s h1 h10 h17
                      | true =>
                        cases h2 : s 2 with
                        | false =>
                          exact color_witness_72 s h2 h10 h17
                        | true =>
                          cases h4 : s 4 with
                          | false =>
                            exact color_witness_71 s h4 h10 h17
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_70 s h5 h10 h17
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_57 s h10 h14 h17
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
                | true =>
                  cases h13 : s 13 with
                  | false =>
                    cases h0 : s 0 with
                    | false =>
                      exact color_witness_64 s h0 h13 h17
                    | true =>
                      cases h1 : s 1 with
                      | false =>
                        exact color_witness_63 s h1 h13 h17
                      | true =>
                        cases h2 : s 2 with
                        | false =>
                          exact color_witness_62 s h2 h13 h17
                        | true =>
                          cases h4 : s 4 with
                          | false =>
                            exact color_witness_61 s h4 h13 h17
                          | true =>
                            cases h5 : s 5 with
                            | false =>
                              exact color_witness_60 s h5 h13 h17
                            | true =>
                              cases h14 : s 14 with
                              | false =>
                                exact color_witness_55 s h13 h14 h17
                              | true =>
                                exact core_witness_0 s h0 h1 h2 h4 h5 h14
                  | true =>
                    exact core_witness_2 s h7 h9 h10 h12 h13 h18
            | true =>
              exact core_witness_1 s h7 h8 h9 h11 h12 h17

end JT58

#print axioms JT58.every_selection_covered

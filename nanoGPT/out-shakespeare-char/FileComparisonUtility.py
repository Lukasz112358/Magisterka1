import filecmp
import os

def compare_files(file1, file2):
    # Najpierw sprawdzamy, czy pliki w ogóle istnieją
    if not os.path.exists(file1) or not os.path.exists(file2):
        print("Błąd: Jeden z plików nie istnieje.")
        return

    # filecmp.cmp sprawdza rozmiar, a potem treść plików
    # shallow=False wymusza sprawdzenie zawartości, a nie tylko metadanych
    are_identical = filecmp.cmp(file1, file2, shallow=False)

    if are_identical:
        print(f"Pliki są IDENTYCZNE.")
    else:
        print(f"Pliki RÓŻNIĄ SIĘ od siebie.")

# Przykład użycia dla Twoich plików z Projektu:
path1 = 'ckpt.pkl'
path2 = 'ckpt1.pkl'

compare_files(path1, path2)

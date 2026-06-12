' Inicia o Copa Widget sem janela de console (silencioso na bandeja)
Set sh = CreateObject("WScript.Shell")
base = Left(WScript.ScriptFullName, InStrRev(WScript.ScriptFullName, "\"))
pyw = "C:\Users\fabio.valle\AppData\Local\Programs\Python\Python314\pythonw.exe"
sh.Run """" & pyw & """ """ & base & "copa_widget.py""", 0, False

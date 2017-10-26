/*
 * Copyright 2016 Nick Russler
 * 
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 * 
 *     http://www.apache.org/licenses/LICENSE-2.0
 * 
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package gui;

import java.awt.Color;
import java.awt.Cursor;
import java.awt.EventQueue;
import java.awt.Font;
import java.awt.Toolkit;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.File;
import java.io.IOException;
import java.io.UnsupportedEncodingException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import javax.swing.ButtonGroup;
import javax.swing.DefaultListModel;
import javax.swing.ImageIcon;
import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JFileChooser;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JList;
import javax.swing.JPanel;
import javax.swing.JProgressBar;
import javax.swing.JRadioButton;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.JTextField;
import javax.swing.SwingUtilities;
import javax.swing.UIManager;
import javax.swing.border.TitledBorder;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;
import javax.swing.event.ListDataEvent;
import javax.swing.event.ListDataListener;

import cli.Main;
import mimeparser.MimeMessageConverter;

import com.google.common.base.Strings;
import com.google.common.io.Files;

/**
 * Main Window GUI Class.
 *
 * @author Nick Russler
 */
public class MainWindow {

	private JFrame frmEmlToPdf;
	private JTextField textField;
	private JTextField tfSuffix;
	private JLabel lblConvertingEmail;
	private JProgressBar progressBar;
	private JButton btnStartConversion;

	/**
	 * Launch the application.
	 */
	public static void main(String[] args) {
		try {
			UIManager.setLookAndFeel(UIManager.getSystemLookAndFeelClassName());
		} catch (Exception e) {
			// ignore error
		}

		EventQueue.invokeLater(new Runnable() {
			@Override
			public void run() {
				try {
					MainWindow window = new MainWindow();
					window.frmEmlToPdf.setVisible(true);
				} catch (Exception e) {
					e.printStackTrace();
				}
			}
		});
	}

	/**
	 * Create the application.
	 */
	public MainWindow() {
		initialize();
	}

	/**
	 * Initialize the contents of the frame.
	 */
	private void initialize() {
		frmEmlToPdf = new JFrame();
		frmEmlToPdf.setIconImage(Toolkit.getDefaultToolkit().getImage(MainWindow.class.getResource("/icons/logo_emlconverter-482_16x16.png")));
		frmEmlToPdf.setResizable(false);
		frmEmlToPdf.setTitle("EML zu PDF Konvertierer");
		frmEmlToPdf.getContentPane().setBackground(Color.WHITE);
		frmEmlToPdf.setBackground(Color.WHITE);
		frmEmlToPdf.setBounds(100, 100, 700, 720);
		frmEmlToPdf.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
		frmEmlToPdf.getContentPane().setLayout(null);
		frmEmlToPdf.setLocationRelativeTo(null);

		JScrollPane scrollPane = new JScrollPane();
		scrollPane.setBounds(10, 11, 487, 210);
		frmEmlToPdf.getContentPane().add(scrollPane);
		scrollPane.setBorder(new TitledBorder(null, "EML Dateien", TitledBorder.LEADING, TitledBorder.TOP, null, null));
		scrollPane.setBackground(Color.WHITE);

		final JList<String> list = new JList<String>();
		scrollPane.setViewportView(list);
		final DefaultListModel<String> listModel = new DefaultListModel<String>();
		list.setModel(listModel);
		list.setBackground(new Color(255, 255, 255));
		list.setBorder(null);
		listModel.addListDataListener(new ListDataListener() {
			public void contentsChanged() {
				lblConvertingEmail.setText("E-Mail 0 von " + listModel.getSize());
			}

			@Override
			public void intervalRemoved(ListDataEvent e) {
				contentsChanged();
			}

			@Override
			public void intervalAdded(ListDataEvent e) {
				contentsChanged();
			}

			@Override
			public void contentsChanged(ListDataEvent e) {
				contentsChanged();
			}
		});

		final JFileChooser dirChooser = new JFileChooser();
		dirChooser.setFileSelectionMode(JFileChooser.DIRECTORIES_ONLY);

		final JButton btnAddFolder = new JButton("Ordner hinzuf\u00FCgen");
		btnAddFolder.addActionListener(new ActionListener() {
			@Override
			public void actionPerformed(ActionEvent e) {
				if (dirChooser.showOpenDialog(frmEmlToPdf) == JFileChooser.APPROVE_OPTION) {
					btnAddFolder.setEnabled(false);
					frmEmlToPdf.setCursor(Cursor.getPredefinedCursor(Cursor.WAIT_CURSOR));

					SwingUtilities.invokeLater(new Runnable() {
						@Override
						public void run() {
							for (File f : Files.fileTreeTraverser().preOrderTraversal(dirChooser.getSelectedFile())) {
								if (f.getName().endsWith(".eml")) {
									listModel.addElement(f.getAbsolutePath());
								}
							}

							btnAddFolder.setEnabled(true);
							frmEmlToPdf.setCursor(Cursor.getDefaultCursor());
						}
					});
				}
			}
		});
		btnAddFolder.setIcon(new ImageIcon(MainWindow.class.getResource("/icons/folder_add.png")));
		btnAddFolder.setBounds(507, 72, 160, 34);
		frmEmlToPdf.getContentPane().add(btnAddFolder);

		final JFileChooser fileChooser = new JFileChooser();
		fileChooser.setMultiSelectionEnabled(true);

		JButton btnAddFile = new JButton("Datei(en) hinzuf\u00FCgen");
		btnAddFile.setIcon(new ImageIcon(MainWindow.class.getResource("/icons/email_add.png")));
		btnAddFile.addActionListener(new ActionListener() {
			@Override
			public void actionPerformed(ActionEvent e) {
				if (fileChooser.showOpenDialog(frmEmlToPdf) == JFileChooser.APPROVE_OPTION) {
					for (File f : fileChooser.getSelectedFiles()) {
						listModel.addElement(f.getAbsolutePath());
					}
				}
			}
		});
		btnAddFile.setBounds(507, 36, 160, 34);
		frmEmlToPdf.getContentPane().add(btnAddFile);

		JButton btnClearList = new JButton("Alle l\u00F6schen");
		btnClearList.setIcon(new ImageIcon(MainWindow.class.getResource("/icons/cross.png")));
		btnClearList.addActionListener(new ActionListener() {
			@Override
			public void actionPerformed(ActionEvent e) {
				listModel.clear();
			}
		});
		btnClearList.setBounds(507, 154, 160, 34);
		frmEmlToPdf.getContentPane().add(btnClearList);

		JPanel panel = new JPanel();
		panel.setBorder(new TitledBorder(null, "Optionen", TitledBorder.LEADING, TitledBorder.TOP, null, null));
		panel.setBackground(Color.WHITE);
		panel.setBounds(10, 232, 664, 121);
		frmEmlToPdf.getContentPane().add(panel);
		panel.setLayout(null);

		final JCheckBox chckbxAddEmailHeaders = new JCheckBox("E-Mail Kopf anzeigen");
		chckbxAddEmailHeaders.setSelected(true);
		chckbxAddEmailHeaders.setBackground(Color.WHITE);
		chckbxAddEmailHeaders.setBounds(10, 17, 260, 23);
		panel.add(chckbxAddEmailHeaders);


		final JCheckBox chckbxFilter = new JCheckBox("E-Mail Historie herausfiltern");
		chckbxFilter.setSelected(true);
		chckbxFilter.setBackground(Color.WHITE);
		chckbxFilter.setBounds(280, 17, 260, 23);
		panel.add(chckbxFilter);

		final JRadioButton rdbtnAutomaticProxySelection = new JRadioButton("Automatische Proxy-Auswahl");
		rdbtnAutomaticProxySelection.setSelected(true);
		rdbtnAutomaticProxySelection.setEnabled(false);
		rdbtnAutomaticProxySelection.setBackground(Color.WHITE);
		rdbtnAutomaticProxySelection.setBounds(98, 43, 180, 23);
		panel.add(rdbtnAutomaticProxySelection);

		textField = new JTextField();
		textField.setEnabled(false);
		textField.setBounds(352, 44, 290, 20);
		panel.add(textField);
		textField.setColumns(10);

		final JRadioButton rdbtnManual = new JRadioButton("Manuell");
		rdbtnManual.addChangeListener(new ChangeListener() {
			@Override
			public void stateChanged(ChangeEvent e) {
				textField.setEnabled(rdbtnManual.isSelected());
			}
		});
		rdbtnManual.setEnabled(false);
		rdbtnManual.setBackground(Color.WHITE);
		rdbtnManual.setBounds(280, 43, 66, 23);
		panel.add(rdbtnManual);

		ButtonGroup bg = new ButtonGroup();
		bg.add(rdbtnManual);
		bg.add(rdbtnAutomaticProxySelection);

		final JCheckBox chckbxUseProxy = new JCheckBox("Proxy");
		chckbxUseProxy.addChangeListener(new ChangeListener() {
			@Override
			public void stateChanged(ChangeEvent e) {
				rdbtnAutomaticProxySelection.setEnabled(chckbxUseProxy.isSelected());
				rdbtnManual.setEnabled(chckbxUseProxy.isSelected());

				if (!chckbxUseProxy.isSelected()) {
					textField.setEnabled(false);
				}
			}
		});
		chckbxUseProxy.setBackground(Color.WHITE);
		chckbxUseProxy.setBounds(10, 43, 86, 23);
		panel.add(chckbxUseProxy);


		final JCheckBox mergeAttachments = new JCheckBox("Anh\u00E4nge zum PDF hinzuf\u00FCgen");
		mergeAttachments.setSelected(true);
		mergeAttachments.setBackground(Color.WHITE);
		mergeAttachments.setBounds(280, 69, 180, 23);
		panel.add(mergeAttachments);


		final JCheckBox chckbxExtractAttachments = new JCheckBox("Anh\u00E4nge separat ablegen");
		chckbxExtractAttachments.setBackground(Color.WHITE);
		chckbxExtractAttachments.setBounds(10, 69, 180, 23);
		panel.add(chckbxExtractAttachments);


		final JCheckBox chckbxSuffix = new JCheckBox("Dateisuffix");
		chckbxSuffix.setBackground(Color.WHITE);
		chckbxSuffix.setBounds(10, 94, 180, 23);
		chckbxSuffix.addChangeListener(new ChangeListener() {
			@Override
			public void stateChanged(ChangeEvent e) {
				tfSuffix.setEnabled(chckbxSuffix.isSelected());
			}
		});
		panel.add(chckbxSuffix);

		tfSuffix = new JTextField();
		tfSuffix.setEnabled(false);
		tfSuffix.setBounds(352, 95, 290, 20);
		panel.add(tfSuffix);
		tfSuffix.setColumns(10);

		JPanel panelProgress = new JPanel();
		panelProgress.setBorder(new TitledBorder(null, "", TitledBorder.LEADING, TitledBorder.TOP, null, null));
		panelProgress.setBackground(Color.WHITE);
		panelProgress.setBounds(10, 356, 664, 127);
		frmEmlToPdf.getContentPane().add(panelProgress);
		panelProgress.setLayout(null);

		btnStartConversion = new JButton("Konvertierung starten");
		btnStartConversion.setIcon(new ImageIcon(MainWindow.class.getResource("/icons/arrow_refresh.png")));
		btnStartConversion.addActionListener(new ActionListener() {
			@Override
			public void actionPerformed(ActionEvent e) {
				btnStartConversion.setEnabled(false);
				frmEmlToPdf.setCursor(Cursor.getPredefinedCursor(Cursor.WAIT_CURSOR));

				String proxyTmp = null;

				if (chckbxUseProxy.isSelected()) {
					if (rdbtnAutomaticProxySelection.isSelected()) {
						proxyTmp = "auto";
					} else {
						proxyTmp = textField.getText();
					}
				}

				final String proxy = proxyTmp;
				new Thread(new Runnable() {
					@Override
					public void run() {
						startConversion(Collections.list(listModel.elements()), chckbxAddEmailHeaders.isSelected(), proxy, chckbxExtractAttachments.isSelected(), mergeAttachments.isSelected(), chckbxSuffix.isSelected() ? tfSuffix.getText() : null, chckbxFilter.isSelected());
					}
				}).start();
			}
		});
		btnStartConversion.setFont(new Font("Tahoma", Font.BOLD, 14));
		btnStartConversion.setBounds(117, 75, 425, 41);
		panelProgress.add(btnStartConversion);

		progressBar = new JProgressBar();
		progressBar.setBounds(10, 32, 644, 32);
		panelProgress.add(progressBar);

		lblConvertingEmail = new JLabel("E-Mail 0 von 0");
		lblConvertingEmail.setBounds(12, 8, 400, 14);
		panelProgress.add(lblConvertingEmail);

		JButton btnRemoveSelectedFrom = new JButton("Auswahl entfernen");
		btnRemoveSelectedFrom.setIcon(new ImageIcon(MainWindow.class.getResource("/icons/email_delete.png")));
		btnRemoveSelectedFrom.addActionListener(new ActionListener() {
			@Override
			public void actionPerformed(ActionEvent e) {
				for (String s : list.getSelectedValuesList()) {
					listModel.removeElement(s);
				}
			}
		});
		btnRemoveSelectedFrom.setBounds(507, 117, 160, 34);
		frmEmlToPdf.getContentPane().add(btnRemoveSelectedFrom);

		JScrollPane scrollPaneLog = new JScrollPane();
		scrollPaneLog.setBounds(10, 502, 664, 183);
		scrollPaneLog.setBorder(new TitledBorder(null, "Log", TitledBorder.LEADING, TitledBorder.TOP, null, null));
		scrollPaneLog.setBackground(Color.WHITE);
		frmEmlToPdf.getContentPane().add(scrollPaneLog);

		JTextArea textArea = new JTextArea();
		textArea.setFont(new Font("Lucida Console", Font.PLAIN, 12));
		textArea.setForeground(Color.GREEN);
		textArea.setBackground(Color.BLACK);
		textArea.setEditable(false);
		scrollPaneLog.setViewportView(textArea);

		MessageConsole mc = new MessageConsole(textArea);
		try {
			mc.redirectOut(Color.GREEN, null);
			mc.redirectErr(Color.RED, null);
		} catch (UnsupportedEncodingException e1) {
		}

		mc.setContainer(scrollPaneLog);
		mc.setMessageLines(1000);
	}

	/**
	 * Start converting the eml files.
	 *
	 * @param enumeration
	 */
	private void startConversion(List<String> l, boolean showHeaders, String proxy, boolean extractAttachments, boolean mergeAttachments, String suffix, boolean filter) {
		try {
			MimeMessageConverter.resetSerial();
			ArrayList<String> argsOptions = new ArrayList<String>();

			if (!showHeaders) {
				argsOptions.add("--hide-headers");
			}

			if (!Strings.isNullOrEmpty(proxy)) {
				argsOptions.add("--proxy");
				argsOptions.add(proxy);
			}

			if (suffix != null) {
				argsOptions.add("--output-suffix");
				argsOptions.add(suffix);
			}

			if (extractAttachments) {
				argsOptions.add("--extract-attachments");
			}

			if(mergeAttachments) {
				argsOptions.add("--merge-attachments");
			}

			if(filter) {
				argsOptions.add("--filter");
			}

			int listSize = l.size();
			for (int i = 0; i < listSize; i++) {
				String[] args = new String[argsOptions.size() + 1];
				argsOptions.toArray(args);
				args[args.length - 1] = l.get(i);

				try {
					Main.main(args);
				} catch (IOException e1) {
					// ignore this error
				}

				final String text = "E-Mail " + (i + 1) + " von " + listSize;
				final int percent = (int) Math.ceil(((i + 1d) * 100d) / listSize);

				SwingUtilities.invokeLater(new Runnable() {
					@Override
					public void run() {
						lblConvertingEmail.setText(text);
						progressBar.setValue(percent);
					}
				});
			}
		} finally {
			btnStartConversion.setEnabled(true);
			frmEmlToPdf.setCursor(Cursor.getDefaultCursor());
		}
	}
}